import NgtcpRV.Machine
import NgtcpRV.BitLemmas
/-!
# `ngtcp2_ord_stream_id` at the RV64 level
`uint64_t ngtcp2_ord_stream_id(int64_t stream_id)` returns
`(uint64_t)(stream_id >> 2) + 1` (arithmetic shift).  Three instructions, no
memory: full functional correctness at the machine level.
-/
namespace NgtcpRV
open RV64
open NgtcpRV.Bits

/-! ### `ngtcp2_ord_stream_id`: 3 instructions at .text+0x0 (relocated to 0) -/

def ordStreamId_words : List (BitVec 32) :=
  [0x40255513#32,
   0x00150513#32,
   0x00008067#32]

/-- `ngtcp2_ord_stream_id` as decoded by llvm-objdump (`none` = `unimp`). -/
def ordStreamId_llvm : List (Option Instr) :=
  [some (.srai 10 10 2#6),
   some (.addi 10 10 1#12),
   some (.jalr 0 1 0#12)]

def ordStreamId : Program := ⟨0, ordStreamId_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem ordStreamId_decode : ordStreamId_words.map decode = ordStreamId_llvm := by decide

@[simp] theorem ordStreamId_base : ordStreamId.base = 0#64 := rfl
@[simp] theorem ordStreamId_len : ordStreamId.words.length = 3 := rfl

@[simp] theorem ordStreamId_fetch_0 : ordStreamId.fetch 0#64 = some (.srai 10 10 2#6) := by decide
@[simp] theorem ordStreamId_fetch_1 : ordStreamId.fetch 4#64 = some (.addi 10 10 1#12) := by decide
@[simp] theorem ordStreamId_fetch_2 : ordStreamId.fetch 8#64 = some (.jalr 0 1 0#12) := by decide


/-- `ngtcp2_ord_stream_id` at the machine level: no memory access, returns to
its caller without faulting, and its result register equals
`(stream_id >>ₐ 2) + 1` — the C expression exactly. -/
theorem ordStreamId_ok (R : Reg → BitVec 64) (ra sid : BitVec 64)
    (m : BitVec 64 → BitVec 8) (rd wr : BitVec 64 → Bool)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 12#64) (hal : ra &&& 3#64 = 0#64)
    (hs : R 10#5 = sid) :
    let s := run ordStreamId 3 { regs := R, pc := 0#64, mem := m, rdok := rd, wrok := wr }
    s.pc = ra ∧ s.fault = false ∧ s.mem = m ∧
    s.rd 10#5 = RV64.srai 2#6 sid + 1#64 := by
  have hj := align_clear0 ra hal
  have hb2 := align_bit1 ra hal
  simp only [run, step_lit, step_ite, step_fault]
  simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
    State.faulted, step_lit, step_ite, step_fault, h1, hj, hb2, hra, hs, RV64.addi]

end NgtcpRV
