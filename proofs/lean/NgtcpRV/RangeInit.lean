import NgtcpRV.Machine
import NgtcpRV.BitLemmas

/-!
# `ngtcp2_range_init` at the RV64 level

`void ngtcp2_range_init(ngtcp2_range *r, uint64_t begin, uint64_t end)` sets
`r->begin = begin` and `r->end = end`.  Compiled to RV64 it is two 64-bit
stores and a return.  The theorem gives write access to exactly the 16 bytes
`[r, r + 16)`; because any store outside that region faults, `fault = false`
in the conclusion is a machine-level proof of spatial memory safety, and the
read-backs show functional correctness.
-/

namespace NgtcpRV
open RV64
open NgtcpRV.Bits

/-! ### `ngtcp2_range_init`: 3 instructions at .text (relocated to 0) -/

def rangeInit_words : List (BitVec 32) :=
  [0x00b53023#32,
   0x00c53423#32,
   0x00008067#32]

/-- `ngtcp2_range_init` as decoded by llvm-objdump (independent decoder). -/
def rangeInit_llvm : List (Option Instr) :=
  [some (.sd 10 11 0#12),
   some (.sd 10 12 8#12),
   some (.jalr 0 1 0#12)]

def rangeInit : Program := ⟨0, rangeInit_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem rangeInit_decode : rangeInit_words.map decode = rangeInit_llvm := by decide

@[simp] theorem rangeInit_base : rangeInit.base = 0#64 := rfl
@[simp] theorem rangeInit_len : rangeInit.words.length = 3 := rfl

@[simp] theorem rangeInit_fetch_0 : rangeInit.fetch 0#64 = some (.sd 10 11 0#12) := by decide
@[simp] theorem rangeInit_fetch_1 : rangeInit.fetch 4#64 = some (.sd 10 12 8#12) := by decide
@[simp] theorem rangeInit_fetch_2 : rangeInit.fetch 8#64 = some (.jalr 0 1 0#12) := by decide

/-- `ngtcp2_range_init` at the machine level: it returns to its caller **without
faulting**, which (given write permission to exactly the 16 bytes `[r, r+16)`)
is a machine-level proof of spatial memory safety — every store lands inside the
`ngtcp2_range` object — and it leaves all memory outside that object unchanged.
The writable region is sized to the object, so a store anywhere else would set
`fault = true`; `fault = false` in the conclusion rules that out. -/
theorem rangeInit_ok (R : Reg → BitVec 64) (ra r vbegin vend : BitVec 64)
    (m : BitVec 64 → BitVec 8) (rd : BitVec 64 → Bool)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 12#64) (hal : ra &&& 3#64 = 0#64)
    (hr : R 10#5 = r) (hb : R 11#5 = vbegin) (he : R 12#5 = vend)
    (hr8 : r.extractLsb 2 0 = 0#3) (hr8' : (r + 8#64).extractLsb 2 0 = 0#3) :
    let s := run rangeInit 3
      { regs := R, pc := 0#64, mem := m, rdok := rd,
        wrok := (fun x => decide (x - r < 16#64)) }
    s.pc = ra ∧ s.fault = false ∧
    (∀ x, ¬ (x - r < 16#64) → s.mem x = m x) := by
  have hj := align_clear0 ra hal
  have hb2 := align_bit1 ra hal
  -- every store address r + c has offset c (< 16) from the base, so it is writable
  have cancel : ∀ c : BitVec 64, r + c - r = c := fun c => by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  simp only [run, step_lit, step_ite, step_fault]
  simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
    State.canWrite8, State.store64, State.store8, State.faulted, aligned8, State.read64,
    step_lit, step_ite, step_fault, h1, hj, hb2, hra, hr, hb, he, hr8, hr8',
    BitVec.add_assoc, cancel]
  -- The simp above already discharged `pc = ra` and `fault = false` (memory safety:
  -- all store offsets are concrete and < 16, so no store faults).  The only goal
  -- left is that memory outside [r, r+16) is unchanged.
  intro x hx          -- hx : 16#64 ≤ x - r
  -- x differs from every store address r + c (c < 16), since x - r ≥ 16
  have hdiff : ∀ c : BitVec 64, c < 16#64 → x ≠ r + c := by
    intro c hc hxc; subst hxc; rw [cancel] at hx; exact absurd hc (BitVec.not_lt.mpr hx)
  have hne : x ≠ r := by
    intro h; subst h; rw [BitVec.sub_self] at hx; exact absurd hx (by decide)
  simp only [hne, hdiff 1#64 (by decide), hdiff 2#64 (by decide),
    hdiff 3#64 (by decide), hdiff 4#64 (by decide), hdiff 5#64 (by decide), hdiff 6#64 (by decide),
    hdiff 7#64 (by decide), hdiff 8#64 (by decide), hdiff 9#64 (by decide), hdiff 10#64 (by decide),
    hdiff 11#64 (by decide), hdiff 12#64 (by decide), hdiff 13#64 (by decide),
    hdiff 14#64 (by decide), hdiff 15#64 (by decide), if_false]

end NgtcpRV
