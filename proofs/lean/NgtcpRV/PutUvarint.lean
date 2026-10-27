import NgtcpRV.Machine
import NgtcpRV.BitLemmas

/-!
# `ngtcp2_put_uvarint` at the RV64 level (memory safety)

The varint encoder writes 1, 2, 4 or 8 bytes at `p` depending on `n`'s
magnitude.  Compiled to RV64 it is 30 byte-stores guarded by magnitude
branches.  With write access to exactly the 8-byte region `[p, p+8)` (the
largest encoding), the theorem shows the run does not fault: every store lands
inside `[p, p+8)` — machine-level spatial write-safety.
-/

namespace NgtcpRV
open RV64
open NgtcpRV.Bits

def putUvarint_words : List (BitVec 32) :=
  [0x03f00613#32,
   0x00b66663#32,
   0x00150613#32,
   0x0b00006f#32,
   0x00e5d613#32,
   0x02061463#32,
   0x00859613#32,
   0x0085d693#32,
   0x0ff6f713#32,
   0x00d50023#32,
   0x00b500a3#32,
   0x00e66733#32,
   0x00250613#32,
   0x04076593#32,
   0x0840006f#32,
   0x01e5d613#32,
   0x02061863#32,
   0x0185d69b#32,
   0x0185d713#32,
   0x0085d793#32,
   0x0105d813#32,
   0x00450613#32,
   0x00e50023#32,
   0x010500a3#32,
   0x00f50123#32,
   0x00b501a3#32,
   0xf806e593#32,
   0x0500006f#32,
   0x03e5d613#32,
   0x04061a63#32,
   0x0385d693#32,
   0x0285d713#32,
   0x0185d613#32,
   0x0085d793#32,
   0x0105d813#32,
   0x0205d893#32,
   0x0305d293#32,
   0x00c50223#32,
   0x010502a3#32,
   0x00f50323#32,
   0x00b503a3#32,
   0x00850613#32,
   0x00d50023#32,
   0x005500a3#32,
   0x00e50123#32,
   0x011501a3#32,
   0xfc06e593#32,
   0x00b50023#32,
   0x00060513#32,
   0x00008067#32,
   0xc0001073#32]

/-- `ngtcp2_put_uvarint` as decoded by llvm-objdump (`none` = `unimp`). -/
def putUvarint_llvm : List (Option Instr) :=
  [some (.addi 12 0 63#12),
   some (.bltu 12 11 12#13),
   some (.addi 12 10 1#12),
   some (.jal 0 176#21),
   some (.srli 12 11 14#6),
   some (.bne 12 0 40#13),
   some (.slli 12 11 8#6),
   some (.srli 13 11 8#6),
   some (.andi 14 13 255#12),
   some (.sb 10 13 0#12),
   some (.sb 10 11 1#12),
   some (.or 14 12 14),
   some (.addi 12 10 2#12),
   some (.ori 11 14 64#12),
   some (.jal 0 132#21),
   some (.srli 12 11 30#6),
   some (.bne 12 0 48#13),
   some (.srliw 13 11 24#5),
   some (.srli 14 11 24#6),
   some (.srli 15 11 8#6),
   some (.srli 16 11 16#6),
   some (.addi 12 10 4#12),
   some (.sb 10 14 0#12),
   some (.sb 10 16 1#12),
   some (.sb 10 15 2#12),
   some (.sb 10 11 3#12),
   some (.ori 11 13 3968#12),
   some (.jal 0 80#21),
   some (.srli 12 11 62#6),
   some (.bne 12 0 84#13),
   some (.srli 13 11 56#6),
   some (.srli 14 11 40#6),
   some (.srli 12 11 24#6),
   some (.srli 15 11 8#6),
   some (.srli 16 11 16#6),
   some (.srli 17 11 32#6),
   some (.srli 5 11 48#6),
   some (.sb 10 12 4#12),
   some (.sb 10 16 5#12),
   some (.sb 10 15 6#12),
   some (.sb 10 11 7#12),
   some (.addi 12 10 8#12),
   some (.sb 10 13 0#12),
   some (.sb 10 5 1#12),
   some (.sb 10 14 2#12),
   some (.sb 10 17 3#12),
   some (.ori 11 13 4032#12),
   some (.sb 10 11 0#12),
   some (.addi 10 12 0#12),
   some (.jalr 0 1 0#12),
   none]

def putUvarint : Program := ⟨0, putUvarint_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem putUvarint_decode : putUvarint_words.map decode = putUvarint_llvm := by decide

@[simp] theorem putUvarint_base : putUvarint.base = 0#64 := rfl
@[simp] theorem putUvarint_len : putUvarint.words.length = 51 := rfl

@[simp] theorem putUvarint_fetch_0 : putUvarint.fetch 0#64 = some (.addi 12 0 63#12) := by decide
@[simp] theorem putUvarint_fetch_1 : putUvarint.fetch 4#64 = some (.bltu 12 11 12#13) := by decide
@[simp] theorem putUvarint_fetch_2 : putUvarint.fetch 8#64 = some (.addi 12 10 1#12) := by decide
@[simp] theorem putUvarint_fetch_3 : putUvarint.fetch 12#64 = some (.jal 0 176#21) := by decide
@[simp] theorem putUvarint_fetch_4 : putUvarint.fetch 16#64 = some (.srli 12 11 14#6) := by decide
@[simp] theorem putUvarint_fetch_5 : putUvarint.fetch 20#64 = some (.bne 12 0 40#13) := by decide
@[simp] theorem putUvarint_fetch_6 : putUvarint.fetch 24#64 = some (.slli 12 11 8#6) := by decide
@[simp] theorem putUvarint_fetch_7 : putUvarint.fetch 28#64 = some (.srli 13 11 8#6) := by decide
@[simp] theorem putUvarint_fetch_8 : putUvarint.fetch 32#64 = some (.andi 14 13 255#12) := by decide
@[simp] theorem putUvarint_fetch_9 : putUvarint.fetch 36#64 = some (.sb 10 13 0#12) := by decide
@[simp] theorem putUvarint_fetch_10 : putUvarint.fetch 40#64 = some (.sb 10 11 1#12) := by decide
@[simp] theorem putUvarint_fetch_11 : putUvarint.fetch 44#64 = some (.or 14 12 14) := by decide
@[simp] theorem putUvarint_fetch_12 : putUvarint.fetch 48#64 = some (.addi 12 10 2#12) := by decide
@[simp] theorem putUvarint_fetch_13 : putUvarint.fetch 52#64 = some (.ori 11 14 64#12) := by decide
@[simp] theorem putUvarint_fetch_14 : putUvarint.fetch 56#64 = some (.jal 0 132#21) := by decide
@[simp] theorem putUvarint_fetch_15 : putUvarint.fetch 60#64 = some (.srli 12 11 30#6) := by decide
@[simp] theorem putUvarint_fetch_16 : putUvarint.fetch 64#64 = some (.bne 12 0 48#13) := by decide
@[simp] theorem putUvarint_fetch_17 : putUvarint.fetch 68#64 = some (.srliw 13 11 24#5) := by decide
@[simp] theorem putUvarint_fetch_18 : putUvarint.fetch 72#64 = some (.srli 14 11 24#6) := by decide
@[simp] theorem putUvarint_fetch_19 : putUvarint.fetch 76#64 = some (.srli 15 11 8#6) := by decide
@[simp] theorem putUvarint_fetch_20 : putUvarint.fetch 80#64 = some (.srli 16 11 16#6) := by decide
@[simp] theorem putUvarint_fetch_21 : putUvarint.fetch 84#64 = some (.addi 12 10 4#12) := by decide
@[simp] theorem putUvarint_fetch_22 : putUvarint.fetch 88#64 = some (.sb 10 14 0#12) := by decide
@[simp] theorem putUvarint_fetch_23 : putUvarint.fetch 92#64 = some (.sb 10 16 1#12) := by decide
@[simp] theorem putUvarint_fetch_24 : putUvarint.fetch 96#64 = some (.sb 10 15 2#12) := by decide
@[simp] theorem putUvarint_fetch_25 : putUvarint.fetch 100#64 = some (.sb 10 11 3#12) := by decide
@[simp] theorem putUvarint_fetch_26 : putUvarint.fetch 104#64 = some (.ori 11 13 3968#12) := by decide
@[simp] theorem putUvarint_fetch_27 : putUvarint.fetch 108#64 = some (.jal 0 80#21) := by decide
@[simp] theorem putUvarint_fetch_28 : putUvarint.fetch 112#64 = some (.srli 12 11 62#6) := by decide
@[simp] theorem putUvarint_fetch_29 : putUvarint.fetch 116#64 = some (.bne 12 0 84#13) := by decide
@[simp] theorem putUvarint_fetch_30 : putUvarint.fetch 120#64 = some (.srli 13 11 56#6) := by decide
@[simp] theorem putUvarint_fetch_31 : putUvarint.fetch 124#64 = some (.srli 14 11 40#6) := by decide
@[simp] theorem putUvarint_fetch_32 : putUvarint.fetch 128#64 = some (.srli 12 11 24#6) := by decide
@[simp] theorem putUvarint_fetch_33 : putUvarint.fetch 132#64 = some (.srli 15 11 8#6) := by decide
@[simp] theorem putUvarint_fetch_34 : putUvarint.fetch 136#64 = some (.srli 16 11 16#6) := by decide
@[simp] theorem putUvarint_fetch_35 : putUvarint.fetch 140#64 = some (.srli 17 11 32#6) := by decide
@[simp] theorem putUvarint_fetch_36 : putUvarint.fetch 144#64 = some (.srli 5 11 48#6) := by decide
@[simp] theorem putUvarint_fetch_37 : putUvarint.fetch 148#64 = some (.sb 10 12 4#12) := by decide
@[simp] theorem putUvarint_fetch_38 : putUvarint.fetch 152#64 = some (.sb 10 16 5#12) := by decide
@[simp] theorem putUvarint_fetch_39 : putUvarint.fetch 156#64 = some (.sb 10 15 6#12) := by decide
@[simp] theorem putUvarint_fetch_40 : putUvarint.fetch 160#64 = some (.sb 10 11 7#12) := by decide
@[simp] theorem putUvarint_fetch_41 : putUvarint.fetch 164#64 = some (.addi 12 10 8#12) := by decide
@[simp] theorem putUvarint_fetch_42 : putUvarint.fetch 168#64 = some (.sb 10 13 0#12) := by decide
@[simp] theorem putUvarint_fetch_43 : putUvarint.fetch 172#64 = some (.sb 10 5 1#12) := by decide
@[simp] theorem putUvarint_fetch_44 : putUvarint.fetch 176#64 = some (.sb 10 14 2#12) := by decide
@[simp] theorem putUvarint_fetch_45 : putUvarint.fetch 180#64 = some (.sb 10 17 3#12) := by decide
@[simp] theorem putUvarint_fetch_46 : putUvarint.fetch 184#64 = some (.ori 11 13 4032#12) := by decide
@[simp] theorem putUvarint_fetch_47 : putUvarint.fetch 188#64 = some (.sb 10 11 0#12) := by decide
@[simp] theorem putUvarint_fetch_48 : putUvarint.fetch 192#64 = some (.addi 10 12 0#12) := by decide
@[simp] theorem putUvarint_fetch_49 : putUvarint.fetch 196#64 = some (.jalr 0 1 0#12) := by decide
@[simp] theorem putUvarint_fetch_50 : putUvarint.fetch 200#64 = none := by decide

/-- `ngtcp2_put_uvarint` at the machine level: with write access to exactly the
8-byte region `[p, p+8)` (the maximum encoding) and the documented precondition
`n < 2^62`, the run returns to its caller **without faulting** — every one of
the byte stores lands inside `[p, p+8)` (machine-level spatial write-safety),
across all four magnitude branches. -/
theorem putUvarint_ok (R : Reg -> BitVec 64) (ra p n : BitVec 64)
    (m : BitVec 64 -> BitVec 8) (rd : BitVec 64 -> Bool)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 204#64) (hal : ra &&& 3#64 = 0#64)
    (hp : R 10#5 = p) (hn : R 11#5 = n) (hn62 : n < 0x4000000000000000#64) :
    let s := run putUvarint 51
      { regs := R, pc := 0#64, mem := m, rdok := rd,
        wrok := (fun x => decide (x - p < 8#64)) }
    s.pc = ra ∧ s.fault = false := by
  have hj := align_clear0 ra hal
  have hb2 := align_bit1 ra hal
  have cancel : ∀ c : BitVec 64, p + c - p = c := fun c => by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  simp only [run, step_lit, step_ite, step_fault]
  simp (config := {maxSteps := 8000000}) [State.next, State.wr, State.rd, State.jump, exec,
    State.canWrite8, State.store8, State.faulted, aligned8,
    step_lit, step_ite, step_fault, h1, hj, hb2, hra, hp, hn, hn62,
    BitVec.add_assoc, cancel]
  -- n < 2^62 kills the assert/trap branch (n >> 62 = 0), so all paths return ra
  have hsh62 : srli (62#6) n = 0#64 := by
    simp only [srli, BitVec.ushiftRight_eq', ushr_eq_zero_iff]
    rw [BitVec.lt_def] at hn62; simpa using hn62
  refine ⟨?_, ?_⟩
  · simp only [apply_ite State.pc, hsh62, ite_true, ite_self]
  · simp only [apply_ite State.fault, hsh62, ite_true, ite_self]

end NgtcpRV
