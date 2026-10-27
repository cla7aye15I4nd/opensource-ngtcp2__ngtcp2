import NgtcpRV.Machine
import NgtcpRV.BitLemmas
/-!
# `ngtcp2_pkt_get_type_long` at the RV64 level
Maps a (version, header-byte) pair to a QUIC long-header packet type via nested
switches.  No memory access, so it cannot fault and returns to its caller.
-/
namespace NgtcpRV
open RV64
open NgtcpRV.Bits

/-! ### `ngtcp2_pkt_get_type_long`: 18 instructions at .text+0x0 (relocated to 0) -/

def getTypeLong_words : List (BitVec 32) :=
  [0x03a59593#32,
   0x00100613#32,
   0x03e5d593#32,
   0x02c50463#32,
   0x6b334637#32,
   0x3cf60613#32,
   0x02c51463#32,
   0x00359593#32,
   0x12111537#32,
   0x01350513#32,
   0x00b555bb#32,
   0x0ff5f513#32,
   0x00008067#32,
   0x01058593#32,
   0x0ff5f513#32,
   0x00008067#32,
   0x00000513#32,
   0x00008067#32]

/-- `ngtcp2_pkt_get_type_long` as decoded by llvm-objdump (`none` = `unimp`). -/
def getTypeLong_llvm : List (Option Instr) :=
  [some (.slli 11 11 58#6),
   some (.addi 12 0 1#12),
   some (.srli 11 11 62#6),
   some (.beq 10 12 40#13),
   some (.lui 12 439092#20),
   some (.addi 12 12 975#12),
   some (.bne 10 12 40#13),
   some (.slli 11 11 3#6),
   some (.lui 10 74001#20),
   some (.addi 10 10 19#12),
   some (.srlw 11 10 11),
   some (.andi 10 11 255#12),
   some (.jalr 0 1 0#12),
   some (.addi 11 11 16#12),
   some (.andi 10 11 255#12),
   some (.jalr 0 1 0#12),
   some (.addi 10 0 0#12),
   some (.jalr 0 1 0#12)]

def getTypeLong : Program := ⟨0, getTypeLong_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem getTypeLong_decode : getTypeLong_words.map decode = getTypeLong_llvm := by decide

@[simp] theorem getTypeLong_base : getTypeLong.base = 0#64 := rfl
@[simp] theorem getTypeLong_len : getTypeLong.words.length = 18 := rfl

@[simp] theorem getTypeLong_fetch_0 : getTypeLong.fetch 0#64 = some (.slli 11 11 58#6) := by decide
@[simp] theorem getTypeLong_fetch_1 : getTypeLong.fetch 4#64 = some (.addi 12 0 1#12) := by decide
@[simp] theorem getTypeLong_fetch_2 : getTypeLong.fetch 8#64 = some (.srli 11 11 62#6) := by decide
@[simp] theorem getTypeLong_fetch_3 : getTypeLong.fetch 12#64 = some (.beq 10 12 40#13) := by decide
@[simp] theorem getTypeLong_fetch_4 : getTypeLong.fetch 16#64 = some (.lui 12 439092#20) := by decide
@[simp] theorem getTypeLong_fetch_5 : getTypeLong.fetch 20#64 = some (.addi 12 12 975#12) := by decide
@[simp] theorem getTypeLong_fetch_6 : getTypeLong.fetch 24#64 = some (.bne 10 12 40#13) := by decide
@[simp] theorem getTypeLong_fetch_7 : getTypeLong.fetch 28#64 = some (.slli 11 11 3#6) := by decide
@[simp] theorem getTypeLong_fetch_8 : getTypeLong.fetch 32#64 = some (.lui 10 74001#20) := by decide
@[simp] theorem getTypeLong_fetch_9 : getTypeLong.fetch 36#64 = some (.addi 10 10 19#12) := by decide
@[simp] theorem getTypeLong_fetch_10 : getTypeLong.fetch 40#64 = some (.srlw 11 10 11) := by decide
@[simp] theorem getTypeLong_fetch_11 : getTypeLong.fetch 44#64 = some (.andi 10 11 255#12) := by decide
@[simp] theorem getTypeLong_fetch_12 : getTypeLong.fetch 48#64 = some (.jalr 0 1 0#12) := by decide
@[simp] theorem getTypeLong_fetch_13 : getTypeLong.fetch 52#64 = some (.addi 11 11 16#12) := by decide
@[simp] theorem getTypeLong_fetch_14 : getTypeLong.fetch 56#64 = some (.andi 10 11 255#12) := by decide
@[simp] theorem getTypeLong_fetch_15 : getTypeLong.fetch 60#64 = some (.jalr 0 1 0#12) := by decide
@[simp] theorem getTypeLong_fetch_16 : getTypeLong.fetch 64#64 = some (.addi 10 0 0#12) := by decide
@[simp] theorem getTypeLong_fetch_17 : getTypeLong.fetch 68#64 = some (.jalr 0 1 0#12) := by decide


/-- `ngtcp2_pkt_get_type_long` performs no memory access, so it cannot fault
and returns to its caller. -/
theorem getTypeLong_ok (R : Reg → BitVec 64) (ra : BitVec 64)
    (m : BitVec 64 → BitVec 8) (rd wr : BitVec 64 → Bool)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 72#64) (hal : ra &&& 3#64 = 0#64) :
    let s := run getTypeLong 18 { regs := R, pc := 0#64, mem := m, rdok := rd, wrok := wr }
    s.pc = ra ∧ s.fault = false := by
  have hj := align_clear0 ra hal
  have hb2 := align_bit1 ra hal
  simp only [run, step_lit, step_ite, step_fault]
  simp (config := {maxSteps := 8000000}) [State.next, State.wr, State.rd, State.jump, exec,
    State.faulted, step_lit, step_ite, step_fault, h1, hj, hb2, hra]
  refine ⟨?_, ?_⟩
  · simp only [apply_ite State.pc, ite_self]
  · simp only [apply_ite State.fault, ite_self]

end NgtcpRV
