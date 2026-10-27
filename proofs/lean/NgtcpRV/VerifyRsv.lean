import NgtcpRV.Machine
import NgtcpRV.BitLemmas
/-!
# `ngtcp2_pkt_verify_reserved_bits` at the RV64 level
Pure bit test on the first header byte; the compiler made it branchless (9
instrs, no memory access).  No load/store can fault, so `fault = false` is
immediate; the proof is full machine-level correctness of the control flow.
-/
namespace NgtcpRV
open RV64
open NgtcpRV.Bits

/-! ### `ngtcp2_pkt_verify_reserved_bits`: 9 instructions at .text+0x0 (relocated to 0) -/

def verifyRsv_words : List (BitVec 32) :=
  [0x03851593#32,
   0x43f5d593#32,
   0x0f45f593#32,
   0x01858593#32,
   0x00a5f533#32,
   0x00153513#32,
   0xfff50513#32,
   0xf3757513#32,
   0x00008067#32]

/-- `ngtcp2_pkt_verify_reserved_bits` as decoded by llvm-objdump (`none` = `unimp`). -/
def verifyRsv_llvm : List (Option Instr) :=
  [some (.slli 11 10 56#6),
   some (.srai 11 11 63#6),
   some (.andi 11 11 244#12),
   some (.addi 11 11 24#12),
   some (.and 10 11 10),
   some (.sltiu 10 10 1#12),
   some (.addi 10 10 4095#12),
   some (.andi 10 10 3895#12),
   some (.jalr 0 1 0#12)]

def verifyRsv : Program := ⟨0, verifyRsv_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem verifyRsv_decode : verifyRsv_words.map decode = verifyRsv_llvm := by decide

@[simp] theorem verifyRsv_base : verifyRsv.base = 0#64 := rfl
@[simp] theorem verifyRsv_len : verifyRsv.words.length = 9 := rfl

@[simp] theorem verifyRsv_fetch_0 : verifyRsv.fetch 0#64 = some (.slli 11 10 56#6) := by decide
@[simp] theorem verifyRsv_fetch_1 : verifyRsv.fetch 4#64 = some (.srai 11 11 63#6) := by decide
@[simp] theorem verifyRsv_fetch_2 : verifyRsv.fetch 8#64 = some (.andi 11 11 244#12) := by decide
@[simp] theorem verifyRsv_fetch_3 : verifyRsv.fetch 12#64 = some (.addi 11 11 24#12) := by decide
@[simp] theorem verifyRsv_fetch_4 : verifyRsv.fetch 16#64 = some (.and 10 11 10) := by decide
@[simp] theorem verifyRsv_fetch_5 : verifyRsv.fetch 20#64 = some (.sltiu 10 10 1#12) := by decide
@[simp] theorem verifyRsv_fetch_6 : verifyRsv.fetch 24#64 = some (.addi 10 10 4095#12) := by decide
@[simp] theorem verifyRsv_fetch_7 : verifyRsv.fetch 28#64 = some (.andi 10 10 3895#12) := by decide
@[simp] theorem verifyRsv_fetch_8 : verifyRsv.fetch 32#64 = some (.jalr 0 1 0#12) := by decide


/-- `ngtcp2_pkt_verify_reserved_bits` performs no memory access, so it cannot
fault, and returns to its caller. -/
theorem verifyRsv_ok (R : Reg → BitVec 64) (ra c : BitVec 64)
    (m : BitVec 64 → BitVec 8) (rd wr : BitVec 64 → Bool)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 36#64) (hal : ra &&& 3#64 = 0#64)
    (hc : R 10#5 = c) :
    let s := run verifyRsv 9 { regs := R, pc := 0#64, mem := m, rdok := rd, wrok := wr }
    s.pc = ra ∧ s.fault = false := by
  have hj := align_clear0 ra hal
  have hb2 := align_bit1 ra hal
  simp only [run, step_lit, step_ite, step_fault]
  simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
    State.faulted, step_lit, step_ite, step_fault, h1, hj, hb2, hra, hc]

end NgtcpRV
