import NgtcpRV.Machine
import NgtcpRV.BitLemmas

/-!
# `ngtcp2_range_len` at the RV64 level

`uint64_t ngtcp2_range_len(const ngtcp2_range *r)` returns `r->end - r->begin`.
Compiled to RV64: two loads and a subtract.  The theorem gives read access to
exactly `[r, r+16)`; `fault = false` proves spatial read-safety, no store
changes memory, and the result register holds `read64(r+8) - read64(r)` — the
difference of the two fields, matching the C source.
-/
namespace NgtcpRV
open RV64
open NgtcpRV.Bits

/-! ### `ngtcp2_range_len`: 4 instructions at .text+0xc (relocated to 0) -/

def rangeLen_words : List (BitVec 32) :=
  [0x00053583#32,
   0x00853503#32,
   0x40b50533#32,
   0x00008067#32]

/-- `ngtcp2_range_len` as decoded by llvm-objdump (`none` = `unimp`). -/
def rangeLen_llvm : List (Option Instr) :=
  [some (.ld 11 10 0#12),
   some (.ld 10 10 8#12),
   some (.sub 10 10 11),
   some (.jalr 0 1 0#12)]

def rangeLen : Program := ⟨0, rangeLen_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem rangeLen_decode : rangeLen_words.map decode = rangeLen_llvm := by decide

@[simp] theorem rangeLen_base : rangeLen.base = 0#64 := rfl
@[simp] theorem rangeLen_len : rangeLen.words.length = 4 := rfl

@[simp] theorem rangeLen_fetch_0 : rangeLen.fetch 0#64 = some (.ld 11 10 0#12) := by decide
@[simp] theorem rangeLen_fetch_1 : rangeLen.fetch 4#64 = some (.ld 10 10 8#12) := by decide
@[simp] theorem rangeLen_fetch_2 : rangeLen.fetch 8#64 = some (.sub 10 10 11) := by decide
@[simp] theorem rangeLen_fetch_3 : rangeLen.fetch 12#64 = some (.jalr 0 1 0#12) := by decide


/-- `ngtcp2_range_len` at the machine level: with read access to exactly the
16-byte object, it returns without faulting (spatial read-safety), leaves
memory unchanged, and its result register is `end - begin`. -/
theorem rangeLen_ok (R : Reg → BitVec 64) (ra r : BitVec 64)
    (m : BitVec 64 → BitVec 8) (wr : BitVec 64 → Bool)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 16#64) (hal : ra &&& 3#64 = 0#64)
    (hr : R 10#5 = r)
    (hr0 : r.extractLsb 2 0 = 0#3) (hr8 : (r + 8#64).extractLsb 2 0 = 0#3) :
    let s := run rangeLen 4
      { regs := R, pc := 0#64, mem := m,
        rdok := (fun x => decide (x - r < 16#64)), wrok := wr }
    s.pc = ra ∧ s.fault = false ∧ s.mem = m ∧
    s.rd 10#5 = s.read64 (r + 8#64) - s.read64 r := by
  have hj := align_clear0 ra hal
  have hb2 := align_bit1 ra hal
  have cancel : ∀ c : BitVec 64, r + c - r = c := fun c => by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  simp only [run, step_lit, step_ite, step_fault]
  simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
    State.canRead8, State.read64, State.faulted, aligned8,
    step_lit, step_ite, step_fault, h1, hj, hb2, hra, hr, hr0, hr8,
    BitVec.add_assoc, cancel, RV64.sub]

end NgtcpRV
