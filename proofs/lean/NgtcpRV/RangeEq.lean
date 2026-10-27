import NgtcpRV.Machine
import NgtcpRV.BitLemmas
/-!
# `ngtcp2_range_eq` at the RV64 level (read memory safety)
`int ngtcp2_range_eq(const ngtcp2_range *a, const ngtcp2_range *b)` loads the
two 16-byte objects and compares them with short-circuit branches.  With read
access to exactly `[a,a+16)` and `[b,b+16)`, the run does not fault: spatial
read-safety on every path.
-/
namespace NgtcpRV
open RV64
open NgtcpRV.Bits

/-! ### `ngtcp2_range_eq`: 10 instructions at .text+0x1c (relocated to 0) -/

def rangeEq_words : List (BitVec 32) :=
  [0x00053603#32,
   0x0005b683#32,
   0x00d61c63#32,
   0x00853503#32,
   0x0085b583#32,
   0x00b54533#32,
   0x00153513#32,
   0x00008067#32,
   0x00000513#32,
   0x00008067#32]

/-- `ngtcp2_range_eq` as decoded by llvm-objdump (`none` = `unimp`). -/
def rangeEq_llvm : List (Option Instr) :=
  [some (.ld 12 10 0#12),
   some (.ld 13 11 0#12),
   some (.bne 12 13 24#13),
   some (.ld 10 10 8#12),
   some (.ld 11 11 8#12),
   some (.xor 10 10 11),
   some (.sltiu 10 10 1#12),
   some (.jalr 0 1 0#12),
   some (.addi 10 0 0#12),
   some (.jalr 0 1 0#12)]

def rangeEq : Program := ⟨0, rangeEq_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem rangeEq_decode : rangeEq_words.map decode = rangeEq_llvm := by decide

@[simp] theorem rangeEq_base : rangeEq.base = 0#64 := rfl
@[simp] theorem rangeEq_len : rangeEq.words.length = 10 := rfl

@[simp] theorem rangeEq_fetch_0 : rangeEq.fetch 0#64 = some (.ld 12 10 0#12) := by decide
@[simp] theorem rangeEq_fetch_1 : rangeEq.fetch 4#64 = some (.ld 13 11 0#12) := by decide
@[simp] theorem rangeEq_fetch_2 : rangeEq.fetch 8#64 = some (.bne 12 13 24#13) := by decide
@[simp] theorem rangeEq_fetch_3 : rangeEq.fetch 12#64 = some (.ld 10 10 8#12) := by decide
@[simp] theorem rangeEq_fetch_4 : rangeEq.fetch 16#64 = some (.ld 11 11 8#12) := by decide
@[simp] theorem rangeEq_fetch_5 : rangeEq.fetch 20#64 = some (.xor 10 10 11) := by decide
@[simp] theorem rangeEq_fetch_6 : rangeEq.fetch 24#64 = some (.sltiu 10 10 1#12) := by decide
@[simp] theorem rangeEq_fetch_7 : rangeEq.fetch 28#64 = some (.jalr 0 1 0#12) := by decide
@[simp] theorem rangeEq_fetch_8 : rangeEq.fetch 32#64 = some (.addi 10 0 0#12) := by decide
@[simp] theorem rangeEq_fetch_9 : rangeEq.fetch 36#64 = some (.jalr 0 1 0#12) := by decide


/-- `ngtcp2_range_eq` reads only inside the two 16-byte argument objects: the
run never faults (spatial read-safety across the short-circuit branches). -/
theorem rangeEq_safe (R : Reg → BitVec 64) (ra a b : BitVec 64)
    (m : BitVec 64 → BitVec 8) (wr : BitVec 64 → Bool)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 40#64) (hal : ra &&& 3#64 = 0#64)
    (ha : R 10#5 = a) (hb : R 11#5 = b)
    (ha0 : a.extractLsb 2 0 = 0#3) (ha8 : (a + 8#64).extractLsb 2 0 = 0#3)
    (hb0 : b.extractLsb 2 0 = 0#3) (hb8 : (b + 8#64).extractLsb 2 0 = 0#3) :
    (run rangeEq 10
      { regs := R, pc := 0#64, mem := m,
        rdok := (fun x => decide (x - a < 16#64) || decide (x - b < 16#64)), wrok := wr }).fault
      = false := by
  have hj := align_clear0 ra hal
  have hb2 := align_bit1 ra hal
  have cancelA : ∀ c : BitVec 64, a + c - a = c := fun c => by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  have cancelB : ∀ c : BitVec 64, b + c - b = c := fun c => by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  simp only [run, step_lit, step_ite, step_fault]
  simp (config := {maxSteps := 8000000}) [State.next, State.wr, State.rd, State.jump, exec,
    State.canRead8, State.read64, State.faulted, aligned8,
    step_lit, step_ite, step_fault, h1, hj, hb2, hra, ha, hb, ha0, ha8, hb0, hb8,
    BitVec.add_assoc, cancelA, cancelB]
  simp only [apply_ite State.fault, ite_self]

end NgtcpRV
