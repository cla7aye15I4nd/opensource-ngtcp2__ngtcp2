import NgtcpRV.Machine
import NgtcpRV.BitLemmas
/-!
# `ngtcp2_is_reserved_version` / `ngtcp2_is_supported_version` at the RV64 level
Both are pure predicates on a 32-bit version with no memory access: they cannot
fault and return to their caller.
-/
namespace NgtcpRV
open RV64
open NgtcpRV.Bits

/-! ### `ngtcp2_is_reserved_version`: 6 instructions at .text+0x0 (relocated to 0) -/

def isReserved_words : List (BitVec 32) :=
  [0x0a0a15b7#32,
   0xa0a58593#32,
   0x00b57533#32,
   0x00b54533#32,
   0x00153513#32,
   0x00008067#32]

/-- `ngtcp2_is_reserved_version` as decoded by llvm-objdump (`none` = `unimp`). -/
def isReserved_llvm : List (Option Instr) :=
  [some (.lui 11 41121#20),
   some (.addi 11 11 2570#12),
   some (.and 10 10 11),
   some (.xor 10 10 11),
   some (.sltiu 10 10 1#12),
   some (.jalr 0 1 0#12)]

def isReserved : Program := ⟨0, isReserved_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem isReserved_decode : isReserved_words.map decode = isReserved_llvm := by decide

@[simp] theorem isReserved_base : isReserved.base = 0#64 := rfl
@[simp] theorem isReserved_len : isReserved.words.length = 6 := rfl

@[simp] theorem isReserved_fetch_0 : isReserved.fetch 0#64 = some (.lui 11 41121#20) := by decide
@[simp] theorem isReserved_fetch_1 : isReserved.fetch 4#64 = some (.addi 11 11 2570#12) := by decide
@[simp] theorem isReserved_fetch_2 : isReserved.fetch 8#64 = some (.and 10 10 11) := by decide
@[simp] theorem isReserved_fetch_3 : isReserved.fetch 12#64 = some (.xor 10 10 11) := by decide
@[simp] theorem isReserved_fetch_4 : isReserved.fetch 16#64 = some (.sltiu 10 10 1#12) := by decide
@[simp] theorem isReserved_fetch_5 : isReserved.fetch 20#64 = some (.jalr 0 1 0#12) := by decide


/-! ### `ngtcp2_is_supported_version`: 8 instructions at .text+0x18 (relocated to 0) -/

def isSupported_words : List (BitVec 32) :=
  [0xfff50593#32,
   0x6b334637#32,
   0x0015b593#32,
   0x3cf60613#32,
   0x00c54533#32,
   0x00153513#32,
   0x00a5e533#32,
   0x00008067#32]

/-- `ngtcp2_is_supported_version` as decoded by llvm-objdump (`none` = `unimp`). -/
def isSupported_llvm : List (Option Instr) :=
  [some (.addi 11 10 4095#12),
   some (.lui 12 439092#20),
   some (.sltiu 11 11 1#12),
   some (.addi 12 12 975#12),
   some (.xor 10 10 12),
   some (.sltiu 10 10 1#12),
   some (.or 10 11 10),
   some (.jalr 0 1 0#12)]

def isSupported : Program := ⟨0, isSupported_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem isSupported_decode : isSupported_words.map decode = isSupported_llvm := by decide

@[simp] theorem isSupported_base : isSupported.base = 0#64 := rfl
@[simp] theorem isSupported_len : isSupported.words.length = 8 := rfl

@[simp] theorem isSupported_fetch_0 : isSupported.fetch 0#64 = some (.addi 11 10 4095#12) := by decide
@[simp] theorem isSupported_fetch_1 : isSupported.fetch 4#64 = some (.lui 12 439092#20) := by decide
@[simp] theorem isSupported_fetch_2 : isSupported.fetch 8#64 = some (.sltiu 11 11 1#12) := by decide
@[simp] theorem isSupported_fetch_3 : isSupported.fetch 12#64 = some (.addi 12 12 975#12) := by decide
@[simp] theorem isSupported_fetch_4 : isSupported.fetch 16#64 = some (.xor 10 10 12) := by decide
@[simp] theorem isSupported_fetch_5 : isSupported.fetch 20#64 = some (.sltiu 10 10 1#12) := by decide
@[simp] theorem isSupported_fetch_6 : isSupported.fetch 24#64 = some (.or 10 11 10) := by decide
@[simp] theorem isSupported_fetch_7 : isSupported.fetch 28#64 = some (.jalr 0 1 0#12) := by decide


theorem isReserved_ok (R : Reg → BitVec 64) (ra : BitVec 64)
    (m : BitVec 64 → BitVec 8) (rd wr : BitVec 64 → Bool)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 24#64) (hal : ra &&& 3#64 = 0#64) :
    let s := run isReserved 6 { regs := R, pc := 0#64, mem := m, rdok := rd, wrok := wr }
    s.pc = ra ∧ s.fault = false := by
  have hj := align_clear0 ra hal
  have hb2 := align_bit1 ra hal
  simp only [run, step_lit, step_ite, step_fault]
  simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
    State.faulted, step_lit, step_ite, step_fault, h1, hj, hb2, hra]

theorem isSupported_ok (R : Reg → BitVec 64) (ra : BitVec 64)
    (m : BitVec 64 → BitVec 8) (rd wr : BitVec 64 → Bool)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 32#64) (hal : ra &&& 3#64 = 0#64) :
    let s := run isSupported 8 { regs := R, pc := 0#64, mem := m, rdok := rd, wrok := wr }
    s.pc = ra ∧ s.fault = false := by
  have hj := align_clear0 ra hal
  have hb2 := align_bit1 ra hal
  simp only [run, step_lit, step_ite, step_fault]
  simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
    State.faulted, step_lit, step_ite, step_fault, h1, hj, hb2, hra]

end NgtcpRV
