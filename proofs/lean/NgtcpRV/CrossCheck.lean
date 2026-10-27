import NgtcpRV.AdjustPktNum
import Std.Tactic.BVDecide

/-!
# Independent cross-check with `bv_decide` (SAT + LRAT)

The same statements as in `NgtcpRV.AdjustPktNum`, re-proven by a different
engine: `bv_decide` bit-blasts each goal to SAT, solves it with CaDiCaL, and
checks the LRAT certificate.  Note that in this Lean version the certificate
is checked by compiled code (`Lean.Meta.nativeEqTrue`), so these proofs depend
on `*._native.bv_decide.ax_*` axioms; they are a second, differently-trusted
witness, NOT the primary kernel-checked proofs.
-/

namespace NgtcpRV.CrossCheck
open NgtcpRV

/-! ## Layer 1: the machine code computes the C function

For every initial register file, running the 21 instructions from the entry
point returns to the caller (`pc = ra`) without a fault and leaves in `a0`
exactly the value of the C source under `uint64_t` semantics.  The only
assumptions are the calling convention (`a0..a2` = arguments, `ra` = return
address, which lies outside the function and is 4-byte aligned) and
`pkt_numlen < 8`, without which `1ULL << (pkt_numlen * 8)` is undefined in C. -/

set_option maxHeartbeats 2000000 in
theorem bv_adjustPktNum_machine_eq_C (R : Reg → BitVec 64) (ra : BitVec 64)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 84#64) (hal : ra &&& 3#64 = 0#64)
    (hlen : R 12#5 < 8#64) :
    let s := run adjustPktNum 19 {regs := R, pc := 0#64}
    s.pc = ra ∧ s.fault = false ∧ s.rd 10#5 = adjustC (R 10#5) (R 11#5) (R 12#5) := by
  have hj : ra &&& 18446744073709551614#64 = ra := by bv_decide
  have hb : ra.extractLsb 1 1 = 0#1 := by bv_decide
  simp only [run, step_lit, step_ite]
  simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
    step_lit, step_ite, h1, hj, hb, hra]
  refine ⟨?_, ?_, ?_⟩
  · rw [apply_ite State.pc]; simp
  · rw [apply_ite State.fault]; simp
  · have hl : R 12#5 = 0#64 ∨ R 12#5 = 1#64 ∨ R 12#5 = 2#64 ∨ R 12#5 = 3#64 ∨
        R 12#5 = 4#64 ∨ R 12#5 = 5#64 ∨ R 12#5 = 6#64 ∨ R 12#5 = 7#64 := by bv_decide
    simp only [apply_ite State.regs, ite_app]
    rcases hl with h|h|h|h|h|h|h|h <;>
      simp [h, adjustC, RV64.add, RV64.sub, RV64.and, RV64.or, RV64.sll, RV64.srli,
        RV64.slli, RV64.sltu, RV64.xori, RV64.addi] <;> bv_decide

/-! ## Layer 2 (cross-check)

`MAX = 2^62 - 1` is `NGTCP2_MAX_PKT_NUM`.  `max_pkt_num` is the largest
packet number received so far, or `-1` (all ones) if none.  Comparisons that
the RFC states over unbounded integers are written over 128-bit vectors of
values below `2^64`, where no wrap-around can occur. -/

/-- RFC 9000 §17.1 / Appendix A.3: if the sender's full packet number `P`
    lies in the window `(expected - hwin, expected + hwin]`, then decoding its
    `8 * len` low bits recovers `P` exactly. -/
theorem bv_adjustC_recovers (M P len : BitVec 64) (hpre : Pre M len) (hP : P ≤ MAX)
    (hwin :
      let e := (M + 1).zeroExtend 128
      let hw := (1#128 <<< (len.zeroExtend 128 * 8 - 1))
      e < P.zeroExtend 128 + hw ∧ P.zeroExtend 128 ≤ e + hw) :
    adjustC M (P &&& ((1#64 <<< (len * 8)) - 1)) len = P := by
  obtain ⟨hM, hl1, hl4⟩ := hpre
  have hl : len = 1#64 ∨ len = 2#64 ∨ len = 3#64 ∨ len = 4#64 := by bv_decide
  simp only [MAX] at hM hP
  rcases hl with h|h|h|h <;> subst h <;> simp only [adjustC] at hwin ⊢ <;> bv_decide

/-- Whenever ngtcp2 accepts the result (`≤ NGTCP2_MAX_PKT_NUM`), it equals the
    RFC reference decoding; and the result always keeps the received bits. -/
theorem bv_adjustC_rfc (M pn len : BitVec 64) (hpre : Pre M len)
    (hpn : pn < 1#64 <<< (len * 8)) :
    (adjustC M pn len ≤ MAX → (adjustC M pn len).zeroExtend 128 = rfcDecode M pn len) ∧
    adjustC M pn len &&& ((1#64 <<< (len * 8)) - 1) = pn := by
  obtain ⟨hM, hl1, hl4⟩ := hpre
  have hl : len = 1#64 ∨ len = 2#64 ∨ len = 3#64 ∨ len = 4#64 := by bv_decide
  simp only [MAX] at hM ⊢
  rcases hl with h|h|h|h <;> subst h <;> simp only [adjustC, rfcDecode] at hpn ⊢ <;> bv_decide

/-! ## The machine code meets RFC 9000 -/

theorem bv_adjustPktNum_machine_recovers (R : Reg → BitVec 64) (ra P : BitVec 64)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 84#64) (hal : ra &&& 3#64 = 0#64)
    (hpre : Pre (R 10#5) (R 12#5)) (hP : P ≤ MAX)
    (htrunc : R 11#5 = P &&& ((1#64 <<< (R 12#5 * 8)) - 1))
    (hwin :
      let e := (R 10#5 + 1).zeroExtend 128
      let hw := (1#128 <<< ((R 12#5).zeroExtend 128 * 8 - 1))
      e < P.zeroExtend 128 + hw ∧ P.zeroExtend 128 ≤ e + hw) :
    let s := run adjustPktNum 19 {regs := R, pc := 0#64}
    s.pc = ra ∧ s.fault = false ∧ s.rd 10#5 = P := by
  have hlen : R 12#5 < 8#64 := by
    obtain ⟨-, -, h4⟩ := hpre; bv_decide
  obtain ⟨hpc, hf, hv⟩ := bv_adjustPktNum_machine_eq_C R ra h1 hra hal hlen
  exact ⟨hpc, hf, hv.trans (htrunc ▸ bv_adjustC_recovers _ P _ hpre hP hwin)⟩

theorem bv_adjustPktNum_machine_rfc (R : Reg → BitVec 64) (ra : BitVec 64)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 84#64) (hal : ra &&& 3#64 = 0#64)
    (hpre : Pre (R 10#5) (R 12#5)) (hpn : R 11#5 < 1#64 <<< (R 12#5 * 8)) :
    let s := run adjustPktNum 19 {regs := R, pc := 0#64}
    s.pc = ra ∧ s.fault = false ∧
    (s.rd 10#5 ≤ MAX → (s.rd 10#5).zeroExtend 128 = rfcDecode (R 10#5) (R 11#5) (R 12#5)) ∧
    s.rd 10#5 &&& ((1#64 <<< (R 12#5 * 8)) - 1) = R 11#5 := by
  have hlen : R 12#5 < 8#64 := by
    obtain ⟨-, -, h4⟩ := hpre; bv_decide
  obtain ⟨hpc, hf, hv⟩ := bv_adjustPktNum_machine_eq_C R ra h1 hra hal hlen
  simp only at hv ⊢
  rw [hv]
  exact ⟨hpc, hf, bv_adjustC_rfc _ _ _ hpre hpn⟩

end NgtcpRV.CrossCheck
