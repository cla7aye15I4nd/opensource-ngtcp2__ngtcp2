import NgtcpRV.Tier1Progs
import NgtcpRV.BitLemmas

/-!
# `ngtcp2_get_uvarint` and `ngtcp2_get_uvarintlen` at the RV64 level

Specification (RFC 9000 §16): the two most significant bits of the first
byte give the encoded length `1 << prefix` (1, 2, 4 or 8 bytes); the value is
the remaining bits of those bytes read as a big-endian integer.

The theorems give the functions read access to exactly the encoded bytes
`[p, p + len)` and write access to exactly `[dest, dest + 8)`; because any
other access faults, "no fault" is a memory-safety proof.  All proofs are
kernel-checked (no `bv_decide`, no `native_decide`).
-/

namespace NgtcpRV
open NgtcpRV.Bits

theorem idx64 (i : Nat) (h : i < 64) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega

/-- RFC 9000 §16: encoded length selected by the 2-bit prefix of the first byte. -/
def varintLen (b0 : BitVec 8) : BitVec 64 := 1#64 <<< ((b0.setWidth 64) >>> 6).toNat

/-- RFC 9000 §16: the decoded value of the varint starting at `p`. -/
def varintValue (m : BitVec 64 → BitVec 8) (p : BitVec 64) : BitVec 64 :=
  let b := fun (k : BitVec 64) => (m (p + k)).setWidth 64
  let t := (m p).setWidth 64 >>> 6
  if t = 0#64 then b 0 &&& 0x3f#64
  else if t = 1#64 then (b 0 &&& 0x3f#64) <<< 8 ||| b 1
  else if t = 2#64 then (b 0 &&& 0x3f#64) <<< 24 ||| b 1 <<< 16 ||| b 2 <<< 8 ||| b 3
  else (b 0 &&& 0x3f#64) <<< 56 ||| b 1 <<< 48 ||| b 2 <<< 40 ||| b 3 <<< 32 |||
    b 4 <<< 24 ||| b 5 <<< 16 ||| b 6 <<< 8 ||| b 7

theorem prefix_cases (b : BitVec 8) :
    b.setWidth 64 >>> 6 = 0#64 ∨ b.setWidth 64 >>> 6 = 1#64 ∨
    b.setWidth 64 >>> 6 = 2#64 ∨ b.setWidth 64 >>> 6 = 3#64 := by
  have h := b.isLt
  have e : (b.setWidth 64 >>> 6).toNat = b.toNat / 64 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega)]
  have : b.toNat / 64 = 0 ∨ b.toNat / 64 = 1 ∨ b.toNat / 64 = 2 ∨ b.toNat / 64 = 3 := by omega
  rcases this with h|h|h|h
  · left; apply BitVec.eq_of_toNat_eq; simp [e, h]
  · right; left; apply BitVec.eq_of_toNat_eq; simp [e, h]
  · right; right; left; apply BitVec.eq_of_toNat_eq; simp [e, h]
  · right; right; right; apply BitVec.eq_of_toNat_eq; simp [e, h]

/-- `ngtcp2_get_uvarintlen` reads only the first byte and returns `1 << prefix`. -/
theorem getUvarintlen_ok (R : Reg → BitVec 64) (ra p : BitVec 64) (m : BitVec 64 → BitVec 8)
    (wr : BitVec 64 → Bool)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 20#64) (hal : ra &&& 3#64 = 0#64) (hp : R 10#5 = p) :
    let s := run getUvarintlen 5 { regs := R, pc := 0#64, mem := m, rdok := (fun x => decide (x = p)), wrok := wr }
    s.pc = ra ∧ s.fault = false ∧ s.rd 10#5 = varintLen (m p) ∧ s.mem = m := by
  have hj := align_clear0 ra hal
  have hb := align_bit1 ra hal
  simp only [run, step_lit, step_ite, step_fault]
  simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
    State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp]
  simp [varintLen, RV64.sll, RV64.srli, RV64.addi, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq']
  have h8 := (m p).isLt
  have hlt : ((m p).toNat % 18446744073709551616) >>> 6 < 64 := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  simp [Nat.mod_eq_of_lt hlt]

set_option maxHeartbeats 16000000 in
/-- `ngtcp2_get_uvarint` is memory safe, returns `p + len`, stores the RFC 9000
    value at `dest`, and leaves all other memory unchanged. -/
theorem getUvarint_ok (R : Reg → BitVec 64) (ra p dest : BitVec 64) (m : BitVec 64 → BitVec 8)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 344#64) (hal : ra &&& 3#64 = 0#64)
    (hp : R 11#5 = p) (hd : R 10#5 = dest) (hda : dest.extractLsb 2 0 = 0#3) :
    let L := varintLen (m p)
    let s := run getUvarint 60 { regs := R, pc := 0#64, mem := m, rdok := (fun x => decide (x - p < L)), wrok := (fun x => decide (x - dest < 8#64)) }
    s.pc = ra ∧ s.fault = false ∧ s.rd 10#5 = p + L ∧ s.read64 dest = varintValue m p ∧
    (∀ x, ¬ (x - dest < 8#64) → s.mem x = m x) := by
  have hj := align_clear0 ra hal
  have hb := align_bit1 ra hal
  intro L
  rcases prefix_cases (m p) with ht|ht|ht|ht
  all_goals
    -- the prefix fixes bits 6 and 7 of the first byte
    have hb6 := congrArg (fun v => BitVec.getLsbD v 0) ht
    have hb7 := congrArg (fun v => BitVec.getLsbD v 1) ht
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth] at hb6 hb7
    simp at hb6 hb7
    have hL : L = 1#64 <<< ((m p).setWidth 64 >>> 6).toNat := rfl
    rw [ht] at hL; simp at hL
    simp only [run, step_lit, step_ite, step_fault]
    simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
      State.canRead8, State.canWrite8, State.store64, State.store8, State.faulted, aligned8,
      step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hd, hda, RV64.srli, RV64.addi,
      BitVec.ushiftRight_eq', ht, hL, varintValue]
    refine ⟨?_, ?_⟩
    · simp [State.read64, RV64.or, RV64.and, RV64.andi, RV64.lui, RV64.addi, RV64.slli, RV64.srli,
        RV64.srliw]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rcases idx64 i hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp (config := {decide := true}) only [varintValue, RV64.or, RV64.and, RV64.slli, RV64.srli,
        RV64.srliw, RV64.lui, RV64.andi, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_ofNat,
        BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
        BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last,
        BitVec.getLsbD_ofNat, BitVec.getLsbD_of_ge, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
        Nat.reducePow, Nat.reduceLT, ↓reduceIte, Bool.true_and, Bool.false_and, Bool.and_true,
        Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, decide_true,
        decide_false] <;>
      simp [Nat.testBit, hb6, hb7]
    · intro x hx
      have hx' := BitVec.not_lt.mpr hx
      have n0 := ne_add_of_far x dest 0#64 (by decide) hx'
      have n1 := ne_add_of_far x dest 1#64 (by decide) hx'
      have n2 := ne_add_of_far x dest 2#64 (by decide) hx'
      have n3 := ne_add_of_far x dest 3#64 (by decide) hx'
      have n4 := ne_add_of_far x dest 4#64 (by decide) hx'
      have n5 := ne_add_of_far x dest 5#64 (by decide) hx'
      have n6 := ne_add_of_far x dest 6#64 (by decide) hx'
      have n7 := ne_add_of_far x dest 7#64 (by decide) hx'
      simp only [BitVec.add_zero] at n0
      simp [n0, n1, n2, n3, n4, n5, n6, n7]

/-- RFC 9000 §16: the length of the shortest varint encoding of `n`. -/
def uvarintLenSpec (n : BitVec 64) : BitVec 64 :=
  if n.toNat < 2 ^ 6 then 1 else if n.toNat < 2 ^ 14 then 2 else if n.toNat < 2 ^ 30 then 4 else 8

/-- `ngtcp2_put_uvarintlen`: RFC length for valid values, assertion trap otherwise. -/
theorem putUvarintlen_ok (R : Reg → BitVec 64) (ra : BitVec 64) (m : BitVec 64 → BitVec 8)
    (rd wr : BitVec 64 → Bool)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 68#64) (hal : ra &&& 3#64 = 0#64) :
    let s := run putUvarintlen 16 {regs := R, pc := 0#64, mem := m, rdok := rd, wrok := wr}
    ((R 10#5).toNat < 2 ^ 62 → s.pc = ra ∧ s.fault = false ∧ s.rd 10#5 = uvarintLenSpec (R 10#5)
       ∧ s.mem = m) ∧
    (2 ^ 62 ≤ (R 10#5).toNat → s.fault = true) := by
  have hj := align_clear0 ra hal
  have hb := align_bit1 ra hal
  simp only [run, step_lit, step_ite, step_fault]
  simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
    step_lit, step_ite, step_fault, h1, hj, hb, hra]
  simp only [RV64.srli, RV64.addi, BitVec.ushiftRight_eq', ushr_eq_zero_iff, uvarintLenSpec,
    BitVec.le_def]
  have := (R 10#5).isLt
  constructor
  · intro hn
    repeat' split
    all_goals first
      | (simp_all; done)
      | (exfalso; simp_all; omega)
      | (simp_all <;> omega)
  · intro hn
    repeat' split
    all_goals first
      | (simp_all; done)
      | (exfalso; simp_all; omega)
      | (simp_all <;> omega)

theorem varintLen_pfx {m : BitVec 64 → BitVec 8} {p k : BitVec 64}
    (h : (m p).setWidth 64 >>> 6 = k) : varintLen (m p) = 1#64 <<< k.toNat := by
  simp [varintLen, h]
theorem varintValue_pfx0 {m : BitVec 64 → BitVec 8} {p : BitVec 64} (h : (m p).setWidth 64 >>> 6 = 0#64) :
    varintValue m p = (m (p + 0)).setWidth 64 &&& 0x3f#64 := by simp [varintValue, h]
theorem varintValue_pfx1 {m : BitVec 64 → BitVec 8} {p : BitVec 64} (h : (m p).setWidth 64 >>> 6 = 1#64) :
    varintValue m p = ((m (p + 0)).setWidth 64 &&& 0x3f#64) <<< 8 ||| (m (p + 1)).setWidth 64 := by
  simp [varintValue, h]
theorem varintValue_pfx2 {m : BitVec 64 → BitVec 8} {p : BitVec 64} (h : (m p).setWidth 64 >>> 6 = 2#64) :
    varintValue m p = ((m (p + 0)).setWidth 64 &&& 0x3f#64) <<< 24 ||| (m (p + 1)).setWidth 64 <<< 16 |||
      (m (p + 2)).setWidth 64 <<< 8 ||| (m (p + 3)).setWidth 64 := by
  simp [varintValue, h]
theorem varintValue_pfx3 {m : BitVec 64 → BitVec 8} {p : BitVec 64} (h : (m p).setWidth 64 >>> 6 = 3#64) :
    varintValue m p = ((m (p + 0)).setWidth 64 &&& 0x3f#64) <<< 56 ||| (m (p + 1)).setWidth 64 <<< 48 |||
      (m (p + 2)).setWidth 64 <<< 40 ||| (m (p + 3)).setWidth 64 <<< 32 ||| (m (p + 4)).setWidth 64 <<< 24 |||
      (m (p + 5)).setWidth 64 <<< 16 ||| (m (p + 6)).setWidth 64 <<< 8 ||| (m (p + 7)).setWidth 64 := by
  simp [varintValue, h]

/-- Initial state for `ngtcp2_put_uvarint(p, n)`: may write exactly the RFC
    length's worth of bytes at `p`, may read nothing. -/
def putInit (R : Reg → BitVec 64) (m : BitVec 64 → BitVec 8) (p n : BitVec 64) : State :=
  { regs := R, pc := 0#64, mem := m, rdok := (fun _ => false),
    wrok := (fun x => decide (x - p < uvarintLenSpec n)) }

set_option maxHeartbeats 32000000 in
/-- `ngtcp2_put_uvarint` writes the shortest RFC 9000 encoding of `n` -- and
    nothing else -- and returns the end pointer; for `n ≥ 2^62` its assertion
    traps before any memory is written. -/
theorem putUvarint_ok (R : Reg → BitVec 64) (ra p n : BitVec 64) (m : BitVec 64 → BitVec 8)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 204#64) (hal : ra &&& 3#64 = 0#64)
    (hp : R 10#5 = p) (hn : R 11#5 = n) :
    let s := run putUvarint 40 (putInit R m p n)
    (n.toNat < 2 ^ 62 → s.pc = ra ∧ s.fault = false ∧ s.rd 10#5 = p + uvarintLenSpec n ∧
       varintLen (s.mem p) = uvarintLenSpec n ∧ varintValue s.mem p = n ∧
       ∀ x, ¬ (x - p < uvarintLenSpec n) → s.mem x = m x) ∧
    (2 ^ 62 ≤ n.toNat → s.fault = true) := by
  have hj := align_clear0 ra hal
  have hb := align_bit1 ra hal
  dsimp only
  have hnl := n.isLt
  have hcls : n.toNat < 2 ^ 6 ∨ (2 ^ 6 ≤ n.toNat ∧ n.toNat < 2 ^ 14) ∨
      (2 ^ 14 ≤ n.toNat ∧ n.toNat < 2 ^ 30) ∨ (2 ^ 30 ≤ n.toNat ∧ n.toNat < 2 ^ 62) ∨
      2 ^ 62 ≤ n.toNat := by omega
  simp only [Nat.reducePow] at hcls
  rcases hcls with hc | ⟨hc, hc'⟩ | ⟨hc, hc'⟩ | ⟨hc, hc'⟩ | hc
  · -- 1 byte
    have c1 : ¬ (63#64 < n) := by rw [BitVec.lt_def]; simp; omega
    have c2 : True := trivial
    have c3 : True := trivial
    have c4 : True := trivial
    have hL : uvarintLenSpec n = 1#64 := by rw [uvarintLenSpec, if_pos (by simp only [Nat.reducePow]; omega)]; rfl
    have hz := getLsbD_of_lt_pow n 6 (by simp only [Nat.reducePow]; omega)
    have hz' : ∀ (i : Nat) (h : i < 64), 6 ≤ i → n[i] = false := fun i h hi => by
      rw [← BitVec.getLsbD_eq_getElem h]; exact hz i hi
    have hpre : ((run putUvarint 40 (putInit R m p n)).mem p).setWidth 64 >>> 6 = 0#64 := by
      simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rcases idx64 i hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp (config := {decide := true}) only [varintValue, RV64.or, RV64.and, RV64.slli, RV64.srli,
        RV64.srliw, RV64.lui, RV64.andi, RV64.ori, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_ofNat,
        BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
        BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last,
        BitVec.getLsbD_ofNat, BitVec.getLsbD_of_ge, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
        Nat.reducePow, Nat.reduceLT, ↓reduceIte, Bool.true_and, Bool.false_and, Bool.and_true,
        Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, decide_true,
        decide_false] <;>
      simp [Nat.testBit, hz, hz', BitVec.getElem_signExtend, BitVec.getElem_ushiftRight,
        BitVec.getElem_extractLsb', BitVec.msb_eq_getLsbD_last]
    refine ⟨fun _ => ?_, fun _ => by omega⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
    · simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
    · simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
    · rw [varintLen_pfx hpre, hL]; decide
    · rw [varintValue_pfx0 hpre]
      simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rcases idx64 i hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp (config := {decide := true}) only [varintValue, RV64.or, RV64.and, RV64.slli, RV64.srli,
        RV64.srliw, RV64.lui, RV64.andi, RV64.ori, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_ofNat,
        BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
        BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last,
        BitVec.getLsbD_ofNat, BitVec.getLsbD_of_ge, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
        Nat.reducePow, Nat.reduceLT, ↓reduceIte, Bool.true_and, Bool.false_and, Bool.and_true,
        Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, decide_true,
        decide_false] <;>
      simp [Nat.testBit, hz, hz', BitVec.getElem_signExtend, BitVec.getElem_ushiftRight,
        BitVec.getElem_extractLsb', BitVec.msb_eq_getLsbD_last]
    · intro x hx
      have hx' := hx
      rw [hL] at hx'
      simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
      have n0 := ne_add_of_outside x p 0#64 _ (by decide) hx'
      simp only [BitVec.add_zero] at n0
      simp [n0]
  · -- 2 bytes
    have c1 : (63#64 < n) := by rw [BitVec.lt_def]; simp; omega
    have c2 : n >>> 14 = 0#64 := (ushr_eq_zero_iff n 14).mpr (by simp only [Nat.reducePow]; omega)
    have c3 : True := trivial
    have c4 : True := trivial
    have hL : uvarintLenSpec n = 2#64 := by rw [uvarintLenSpec, if_neg (by simp only [Nat.reducePow]; omega), if_pos (by simp only [Nat.reducePow]; omega)]; rfl
    have hz := getLsbD_of_lt_pow n 14 (by simp only [Nat.reducePow]; omega)
    have hz' : ∀ (i : Nat) (h : i < 64), 14 ≤ i → n[i] = false := fun i h hi => by
      rw [← BitVec.getLsbD_eq_getElem h]; exact hz i hi
    have hpre : ((run putUvarint 40 (putInit R m p n)).mem p).setWidth 64 >>> 6 = 1#64 := by
      simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rcases idx64 i hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp (config := {decide := true}) only [varintValue, RV64.or, RV64.and, RV64.slli, RV64.srli,
        RV64.srliw, RV64.lui, RV64.andi, RV64.ori, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_ofNat,
        BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
        BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last,
        BitVec.getLsbD_ofNat, BitVec.getLsbD_of_ge, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
        Nat.reducePow, Nat.reduceLT, ↓reduceIte, Bool.true_and, Bool.false_and, Bool.and_true,
        Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, decide_true,
        decide_false] <;>
      simp [Nat.testBit, hz, hz', BitVec.getElem_signExtend, BitVec.getElem_ushiftRight,
        BitVec.getElem_extractLsb', BitVec.msb_eq_getLsbD_last]
    refine ⟨fun _ => ?_, fun _ => by omega⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
    · simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
    · simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
    · rw [varintLen_pfx hpre, hL]; decide
    · rw [varintValue_pfx1 hpre]
      simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rcases idx64 i hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp (config := {decide := true}) only [varintValue, RV64.or, RV64.and, RV64.slli, RV64.srli,
        RV64.srliw, RV64.lui, RV64.andi, RV64.ori, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_ofNat,
        BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
        BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last,
        BitVec.getLsbD_ofNat, BitVec.getLsbD_of_ge, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
        Nat.reducePow, Nat.reduceLT, ↓reduceIte, Bool.true_and, Bool.false_and, Bool.and_true,
        Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, decide_true,
        decide_false] <;>
      simp [Nat.testBit, hz, hz', BitVec.getElem_signExtend, BitVec.getElem_ushiftRight,
        BitVec.getElem_extractLsb', BitVec.msb_eq_getLsbD_last]
    · intro x hx
      have hx' := hx
      rw [hL] at hx'
      simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
      have n0 := ne_add_of_outside x p 0#64 _ (by decide) hx'; have n1 := ne_add_of_outside x p 1#64 _ (by decide) hx'
      simp only [BitVec.add_zero] at n0
      simp [n0, n1]
  · -- 4 bytes
    have c1 : (63#64 < n) := by rw [BitVec.lt_def]; simp; omega
    have c2 : ¬ n >>> 14 = 0#64 := fun h => by have := (ushr_eq_zero_iff n 14).mp h; omega
    have c3 : n >>> 30 = 0#64 := (ushr_eq_zero_iff n 30).mpr (by simp only [Nat.reducePow]; omega)
    have c4 : True := trivial
    have hL : uvarintLenSpec n = 4#64 := by rw [uvarintLenSpec, if_neg (by simp only [Nat.reducePow]; omega), if_neg (by simp only [Nat.reducePow]; omega), if_pos (by simp only [Nat.reducePow]; omega)]; rfl
    have hz := getLsbD_of_lt_pow n 30 (by simp only [Nat.reducePow]; omega)
    have hz' : ∀ (i : Nat) (h : i < 64), 30 ≤ i → n[i] = false := fun i h hi => by
      rw [← BitVec.getLsbD_eq_getElem h]; exact hz i hi
    have hpre : ((run putUvarint 40 (putInit R m p n)).mem p).setWidth 64 >>> 6 = 2#64 := by
      simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rcases idx64 i hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp (config := {decide := true}) only [varintValue, RV64.or, RV64.and, RV64.slli, RV64.srli,
        RV64.srliw, RV64.lui, RV64.andi, RV64.ori, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_ofNat,
        BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
        BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last,
        BitVec.getLsbD_ofNat, BitVec.getLsbD_of_ge, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
        Nat.reducePow, Nat.reduceLT, ↓reduceIte, Bool.true_and, Bool.false_and, Bool.and_true,
        Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, decide_true,
        decide_false] <;>
      simp [Nat.testBit, hz, hz', BitVec.getElem_signExtend, BitVec.getElem_ushiftRight,
        BitVec.getElem_extractLsb', BitVec.msb_eq_getLsbD_last]
    refine ⟨fun _ => ?_, fun _ => by omega⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
    · simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
    · simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
    · rw [varintLen_pfx hpre, hL]; decide
    · rw [varintValue_pfx2 hpre]
      simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rcases idx64 i hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp (config := {decide := true}) only [varintValue, RV64.or, RV64.and, RV64.slli, RV64.srli,
        RV64.srliw, RV64.lui, RV64.andi, RV64.ori, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_ofNat,
        BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
        BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last,
        BitVec.getLsbD_ofNat, BitVec.getLsbD_of_ge, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
        Nat.reducePow, Nat.reduceLT, ↓reduceIte, Bool.true_and, Bool.false_and, Bool.and_true,
        Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, decide_true,
        decide_false] <;>
      simp [Nat.testBit, hz, hz', BitVec.getElem_signExtend, BitVec.getElem_ushiftRight,
        BitVec.getElem_extractLsb', BitVec.msb_eq_getLsbD_last]
    · intro x hx
      have hx' := hx
      rw [hL] at hx'
      simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
      have n0 := ne_add_of_outside x p 0#64 _ (by decide) hx'; have n1 := ne_add_of_outside x p 1#64 _ (by decide) hx'; have n2 := ne_add_of_outside x p 2#64 _ (by decide) hx'; have n3 := ne_add_of_outside x p 3#64 _ (by decide) hx'
      simp only [BitVec.add_zero] at n0
      simp [n0, n1, n2, n3]
  · -- 8 bytes
    have c1 : (63#64 < n) := by rw [BitVec.lt_def]; simp; omega
    have c2 : ¬ n >>> 14 = 0#64 := fun h => by have := (ushr_eq_zero_iff n 14).mp h; omega
    have c3 : ¬ n >>> 30 = 0#64 := fun h => by have := (ushr_eq_zero_iff n 30).mp h; omega
    have c4 : n >>> 62 = 0#64 := (ushr_eq_zero_iff n 62).mpr (by simp only [Nat.reducePow]; omega)
    have hL : uvarintLenSpec n = 8#64 := by rw [uvarintLenSpec, if_neg (by simp only [Nat.reducePow]; omega), if_neg (by simp only [Nat.reducePow]; omega), if_neg (by simp only [Nat.reducePow]; omega)]; rfl
    have hz := getLsbD_of_lt_pow n 62 (by simp only [Nat.reducePow]; omega)
    have hz' : ∀ (i : Nat) (h : i < 64), 62 ≤ i → n[i] = false := fun i h hi => by
      rw [← BitVec.getLsbD_eq_getElem h]; exact hz i hi
    have hpre : ((run putUvarint 40 (putInit R m p n)).mem p).setWidth 64 >>> 6 = 3#64 := by
      simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rcases idx64 i hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp (config := {decide := true}) only [varintValue, RV64.or, RV64.and, RV64.slli, RV64.srli,
        RV64.srliw, RV64.lui, RV64.andi, RV64.ori, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_ofNat,
        BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
        BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last,
        BitVec.getLsbD_ofNat, BitVec.getLsbD_of_ge, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
        Nat.reducePow, Nat.reduceLT, ↓reduceIte, Bool.true_and, Bool.false_and, Bool.and_true,
        Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, decide_true,
        decide_false] <;>
      simp [Nat.testBit, hz, hz', BitVec.getElem_signExtend, BitVec.getElem_ushiftRight,
        BitVec.getElem_extractLsb', BitVec.msb_eq_getLsbD_last]
    refine ⟨fun _ => ?_, fun _ => by omega⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
    · simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
    · simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
    · rw [varintLen_pfx hpre, hL]; decide
    · rw [varintValue_pfx3 hpre]
      simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rcases idx64 i hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp (config := {decide := true}) only [varintValue, RV64.or, RV64.and, RV64.slli, RV64.srli,
        RV64.srliw, RV64.lui, RV64.andi, RV64.ori, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_ofNat,
        BitVec.extractLsb, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
        BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last,
        BitVec.getLsbD_ofNat, BitVec.getLsbD_of_ge, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
        Nat.reducePow, Nat.reduceLT, ↓reduceIte, Bool.true_and, Bool.false_and, Bool.and_true,
        Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, decide_true,
        decide_false] <;>
      simp [Nat.testBit, hz, hz', BitVec.getElem_signExtend, BitVec.getElem_ushiftRight,
        BitVec.getElem_extractLsb', BitVec.msb_eq_getLsbD_last]
    · intro x hx
      have hx' := hx
      rw [hL] at hx'
      simp only [putInit, run, step_lit, step_ite, step_fault]
      simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
        State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
        RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]
      have n0 := ne_add_of_outside x p 0#64 _ (by decide) hx'; have n1 := ne_add_of_outside x p 1#64 _ (by decide) hx'; have n2 := ne_add_of_outside x p 2#64 _ (by decide) hx'; have n3 := ne_add_of_outside x p 3#64 _ (by decide) hx'; have n4 := ne_add_of_outside x p 4#64 _ (by decide) hx'; have n5 := ne_add_of_outside x p 5#64 _ (by decide) hx'; have n6 := ne_add_of_outside x p 6#64 _ (by decide) hx'; have n7 := ne_add_of_outside x p 7#64 _ (by decide) hx'
      simp only [BitVec.add_zero] at n0
      simp [n0, n1, n2, n3, n4, n5, n6, n7]
  · -- n ≥ 2^62: the assertion traps before any store
    have c1 : 63#64 < n := by rw [BitVec.lt_def]; simp; omega
    have c2 : ¬ n >>> 14 = 0#64 := fun h => by have := (ushr_eq_zero_iff n 14).mp h; omega
    have c3 : ¬ n >>> 30 = 0#64 := fun h => by have := (ushr_eq_zero_iff n 30).mp h; omega
    have c4 : ¬ n >>> 62 = 0#64 := fun h => by have := (ushr_eq_zero_iff n 62).mp h; omega
    have hL : uvarintLenSpec n = 8#64 := by rw [uvarintLenSpec, if_neg (by simp only [Nat.reducePow]; omega), if_neg (by simp only [Nat.reducePow]; omega), if_neg (by simp only [Nat.reducePow]; omega)]; rfl
    refine ⟨fun h => by omega, fun _ => ?_⟩
    simp only [putInit, run, step_lit, step_ite, step_fault]
    simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
      State.store8, State.faulted, step_lit, step_ite, step_fault, h1, hj, hb, hra, hp, hn,
      RV64.srli, RV64.addi, BitVec.ushiftRight_eq', c1, c2, c3, c4, hL]

end NgtcpRV
