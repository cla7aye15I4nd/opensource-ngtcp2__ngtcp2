import NgtcpRV.Machine
import NgtcpRV.BitLemmas
/-!
# `ngtcp2_range_not_after` at the RV64 level
`int ngtcp2_range_not_after(const ngtcp2_range *a, const ngtcp2_range *b)`
returns `a->end <= b->end`.  Branchless: two loads, `sltu`, `xori`.  Full
functional correctness plus read memory-safety.
-/
namespace NgtcpRV
open RV64
open NgtcpRV.Bits

/-! ### `ngtcp2_range_not_after`: 5 instructions at .text+0x0 (relocated to 0) -/

def rangeNotAfter_words : List (BitVec 32) :=
  [0x00853503#32,
   0x0085b583#32,
   0x00a5b533#32,
   0x00154513#32,
   0x00008067#32]

/-- `ngtcp2_range_not_after` as decoded by llvm-objdump (`none` = `unimp`). -/
def rangeNotAfter_llvm : List (Option Instr) :=
  [some (.ld 10 10 8#12),
   some (.ld 11 11 8#12),
   some (.sltu 10 11 10),
   some (.xori 10 10 1#12),
   some (.jalr 0 1 0#12)]

def rangeNotAfter : Program := ⟨0, rangeNotAfter_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem rangeNotAfter_decode : rangeNotAfter_words.map decode = rangeNotAfter_llvm := by decide

@[simp] theorem rangeNotAfter_base : rangeNotAfter.base = 0#64 := rfl
@[simp] theorem rangeNotAfter_len : rangeNotAfter.words.length = 5 := rfl

@[simp] theorem rangeNotAfter_fetch_0 : rangeNotAfter.fetch 0#64 = some (.ld 10 10 8#12) := by decide
@[simp] theorem rangeNotAfter_fetch_1 : rangeNotAfter.fetch 4#64 = some (.ld 11 11 8#12) := by decide
@[simp] theorem rangeNotAfter_fetch_2 : rangeNotAfter.fetch 8#64 = some (.sltu 10 11 10) := by decide
@[simp] theorem rangeNotAfter_fetch_3 : rangeNotAfter.fetch 12#64 = some (.xori 10 10 1#12) := by decide
@[simp] theorem rangeNotAfter_fetch_4 : rangeNotAfter.fetch 16#64 = some (.jalr 0 1 0#12) := by decide


/-- `ngtcp2_range_not_after` at the machine level: reads only the two `end`
fields (no fault), no stores, and its result register is
`(read64(b+8) < read64(a+8)) XOR 1` = `(a->end <= b->end)`. -/
theorem rangeNotAfter_ok (R : Reg → BitVec 64) (ra a b : BitVec 64)
    (m : BitVec 64 → BitVec 8) (wr : BitVec 64 → Bool)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 20#64) (hal : ra &&& 3#64 = 0#64)
    (ha : R 10#5 = a) (hb : R 11#5 = b)
    (ha8 : (a + 8#64).extractLsb 2 0 = 0#3) (hb8 : (b + 8#64).extractLsb 2 0 = 0#3) :
    let s := run rangeNotAfter 5
      { regs := R, pc := 0#64, mem := m,
        rdok := (fun x => decide (x - a < 16#64) || decide (x - b < 16#64)), wrok := wr }
    s.pc = ra ∧ s.fault = false ∧ s.mem = m ∧
    s.rd 10#5 = RV64.xori 1#12 (RV64.sltu (s.read64 (a + 8#64)) (s.read64 (b + 8#64))) := by
  have hj := align_clear0 ra hal
  have hb2 := align_bit1 ra hal
  have cancelA : ∀ c : BitVec 64, a + c - a = c := fun c => by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  have cancelB : ∀ c : BitVec 64, b + c - b = c := fun c => by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  simp only [run, step_lit, step_ite, step_fault]
  simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
    State.canRead8, State.read64, State.faulted, aligned8,
    step_lit, step_ite, step_fault, h1, hj, hb2, hra, ha, hb, ha8, hb8,
    BitVec.add_assoc, cancelA, cancelB]

end NgtcpRV
