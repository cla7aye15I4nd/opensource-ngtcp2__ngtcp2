import NgtcpRV.Machine
import NgtcpRV.BitLemmas

/-!
# `ngtcp2_range_intersect` at the RV64 level

`ngtcp2_range ngtcp2_range_intersect(const ngtcp2_range *a, const ngtcp2_range *b)`
reads the two 16-byte `ngtcp2_range` objects and returns their intersection
(a 16-byte struct returned in `a0`/`a1`).  Compiled to RV64 it is four loads,
two branches selecting `max(a.begin,b.begin)` / `min(a.end,b.end)`, a branchless
emptiness mask, and a return.

The theorem gives read access to exactly the two objects `[a,a+16)` and
`[b,b+16)`; because a load outside a readable region faults, `fault = false`
is a machine-level proof of spatial read-safety.  The function performs no
stores, so memory is unchanged.
-/

namespace NgtcpRV
open RV64
open NgtcpRV.Bits

/-! ### `ngtcp2_range_intersect`: 13 instructions at .text (relocated to 0) -/

def rangeIntersect_words : List (BitVec 32) :=
  [0x00053603#32, 0x0005b683#32, 0x00c6e463#32, 0x00068613#32, 0x00853503#32,
   0x0085b583#32, 0x00b56463#32, 0x00058513#32, 0x00a635b3#32, 0x40b006b3#32,
   0x00a6f5b3#32, 0x00c6f533#32, 0x00008067#32]

def rangeIntersect_llvm : List (Option Instr) :=
  [some (.ld 12 10 0#12), some (.ld 13 11 0#12), some (.bltu 13 12 8#13),
   some (.addi 12 13 0#12), some (.ld 10 10 8#12), some (.ld 11 11 8#12),
   some (.bltu 10 11 8#13), some (.addi 10 11 0#12), some (.sltu 11 12 10),
   some (.sub 13 0 11), some (.and 11 13 10), some (.and 10 13 12),
   some (.jalr 0 1 0#12)]

def rangeIntersect : Program := ⟨0, rangeIntersect_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem rangeIntersect_decode : rangeIntersect_words.map decode = rangeIntersect_llvm := by decide

@[simp] theorem rangeIntersect_base : rangeIntersect.base = 0#64 := rfl
@[simp] theorem rangeIntersect_len : rangeIntersect.words.length = 13 := rfl

@[simp] theorem rangeIntersect_fetch_0 : rangeIntersect.fetch 0#64 = some (.ld 12 10 0#12) := by decide
@[simp] theorem rangeIntersect_fetch_1 : rangeIntersect.fetch 4#64 = some (.ld 13 11 0#12) := by decide
@[simp] theorem rangeIntersect_fetch_2 : rangeIntersect.fetch 8#64 = some (.bltu 13 12 8#13) := by decide
@[simp] theorem rangeIntersect_fetch_3 : rangeIntersect.fetch 12#64 = some (.addi 12 13 0#12) := by decide
@[simp] theorem rangeIntersect_fetch_4 : rangeIntersect.fetch 16#64 = some (.ld 10 10 8#12) := by decide
@[simp] theorem rangeIntersect_fetch_5 : rangeIntersect.fetch 20#64 = some (.ld 11 11 8#12) := by decide
@[simp] theorem rangeIntersect_fetch_6 : rangeIntersect.fetch 24#64 = some (.bltu 10 11 8#13) := by decide
@[simp] theorem rangeIntersect_fetch_7 : rangeIntersect.fetch 28#64 = some (.addi 10 11 0#12) := by decide
@[simp] theorem rangeIntersect_fetch_8 : rangeIntersect.fetch 32#64 = some (.sltu 11 12 10) := by decide
@[simp] theorem rangeIntersect_fetch_9 : rangeIntersect.fetch 36#64 = some (.sub 13 0 11) := by decide
@[simp] theorem rangeIntersect_fetch_10 : rangeIntersect.fetch 40#64 = some (.and 11 13 10) := by decide
@[simp] theorem rangeIntersect_fetch_11 : rangeIntersect.fetch 44#64 = some (.and 10 13 12) := by decide
@[simp] theorem rangeIntersect_fetch_12 : rangeIntersect.fetch 48#64 = some (.jalr 0 1 0#12) := by decide

/-- `ngtcp2_range_intersect` at the machine level: with read access to exactly
the two 16-byte argument objects, it returns to its caller **without faulting**
(spatial read-safety: every load lands inside `[a,a+16)` or `[b,b+16)`) and
performs no stores (memory is unchanged). -/
theorem rangeIntersect_ok (R : Reg → BitVec 64) (ra a b : BitVec 64)
    (m : BitVec 64 → BitVec 8) (wr : BitVec 64 → Bool)
    (h1 : R 1#5 = ra) (hra : ¬ ra < 52#64) (hal : ra &&& 3#64 = 0#64)
    (ha : R 10#5 = a) (hb : R 11#5 = b)
    (ha0 : a.extractLsb 2 0 = 0#3) (ha8 : (a + 8#64).extractLsb 2 0 = 0#3)
    (hb0 : b.extractLsb 2 0 = 0#3) (hb8 : (b + 8#64).extractLsb 2 0 = 0#3) :
    let s := run rangeIntersect 13
      { regs := R, pc := 0#64, mem := m,
        rdok := (fun x => decide (x - a < 16#64) || decide (x - b < 16#64)), wrok := wr }
    s.pc = ra ∧ s.fault = false ∧ s.mem = m := by
  have hj := align_clear0 ra hal
  have hb2 := align_bit1 ra hal
  have cancelA : ∀ c : BitVec 64, a + c - a = c := fun c => by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  have cancelB : ∀ c : BitVec 64, b + c - b = c := fun c => by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  simp only [run, step_lit, step_ite, step_fault]
  simp (config := {maxSteps := 4000000}) [State.next, State.wr, State.rd, State.jump, exec,
    State.canRead8, State.read64, State.faulted, aligned8,
    step_lit, step_ite, step_fault, h1, hj, hb2, hra, ha, hb, ha0, ha8, hb0, hb8,
    BitVec.add_assoc, cancelA, cancelB]
  -- the two data-dependent branches: pc = ra, fault = false, mem = m on every path
  -- (distribute each field projection through the branch `ite`s; every leaf is equal)
  refine ⟨?_, ?_, ?_⟩
  · simp only [apply_ite State.pc, ite_self]
  · simp only [apply_ite State.fault, ite_self]
  · simp only [apply_ite State.mem, ite_self]
