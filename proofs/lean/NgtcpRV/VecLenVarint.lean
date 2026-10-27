/-!
# `ngtcp2_vec_len_varint`: a loop proved by INDUCTION, not by unrolling

The C function sums the lengths of `n` vectors, returning `-1` on overflow:

```c
int64_t ngtcp2_vec_len_varint(const ngtcp2_vec *vec, size_t n) {
  uint64_t res = 0;
  for (i = 0; i < n; ++i) {
    len = vec[i].len;
    if (len > NGTCP2_MAX_VARINT - res) return -1;   // MAX - res < len
    res += len;
  }
  return (int64_t)res;
}
```

Neither CBMC (which unrolls the loop to a fixed bound) nor an instruction-level
`run N` (which unfolds N steps) can cover ALL `n`.  Here instead the loop body
is modelled as a step function over `uint64_t` (faithful: `BitVec 64`, unsigned
`<` and `-` exactly as C), and the whole loop is `List.foldl`.  The safety
invariant is then proved **by induction on the list, for every input of every
size** — the deductive style that scales to loops (and, with more work, to
stateful code) where brute-force expansion cannot.
-/

namespace NgtcpRV.VecLenVarint

/-- `NGTCP2_MAX_VARINT` = 2^62 - 1. -/
def MAXV : BitVec 64 := 0x3FFFFFFFFFFFFFFF#64

/-- One loop iteration, exactly as the C body (`none` models the `-1` return).
`len > MAX - res` is `MAX - res < len` on `uint64_t` (unsigned). -/
def step (acc : Option (BitVec 64)) (len : BitVec 64) : Option (BitVec 64) :=
  match acc with
  | none => none
  | some res => if MAXV - res < len then none else some (res + len)

/-- The whole loop over the `n` vector lengths. -/
def run (lens : List (BitVec 64)) : Option (BitVec 64) :=
  lens.foldl step (some 0#64)

/-- The invariant maintained by every iteration: the accumulator, if live, is a
valid varint value (`≤ MAX`).  This is also exactly what makes the function
safe: with `res ≤ MAX`, `MAX - res` never underflows and `res + len` never wraps
(the guard forces `res + len ≤ MAX < 2^64`). -/
def Inv : Option (BitVec 64) → Prop
  | none => True
  | some r => r ≤ MAXV

/-- `step` preserves the invariant — the heart of the proof, pure bit-vector
arithmetic, no unrolling. -/
theorem step_preserves (acc : Option (BitVec 64)) (len : BitVec 64)
    (h : Inv acc) : Inv (step acc len) := by
  cases acc with
  | none => simp [step, Inv]
  | some res =>
    simp only [Inv] at h
    simp only [step]
    split
    · simp [Inv]          -- overflow path: `none`, trivially safe
    · rename_i hle
      -- ¬ (MAX - res < len), i.e. len ≤ MAX - res; with res ≤ MAX conclude res+len ≤ MAX.
      -- `bv_omega` discharges this bit-vector (mod-2^64) goal with a kernel-checked
      -- certificate, without the kernel ever evaluating 2^64 by recursion.
      simp only [Inv, BitVec.not_lt] at hle ⊢
      bv_omega

/-- **Main result**: for EVERY list of vector lengths — i.e. every `n`, every
input — the loop returns either `-1` (`none`) or a value `≤ MAX`.  Proved by
induction on the list; the loop is never unrolled. -/
theorem run_safe (lens : List (BitVec 64)) : Inv (run lens) := by
  have gen : ∀ (l : List (BitVec 64)) (acc : Option (BitVec 64)),
      Inv acc → Inv (l.foldl step acc) := by
    intro l
    induction l with
    | nil => intro acc h; simpa using h
    | cons x xs ih =>
      intro acc h
      simp only [List.foldl_cons]
      exact ih (step acc x) (step_preserves acc x h)
  exact gen lens (some 0#64) (by simp only [Inv, BitVec.le_def, BitVec.toNat_ofNat]; exact Nat.zero_le _)

/-- Corollary stated the way the C contract reads: the result is never a value
outside the valid varint range, for inputs of unbounded size. -/
theorem run_in_range (lens : List (BitVec 64)) (r : BitVec 64)
    (h : run lens = some r) : r ≤ MAXV := by
  have := run_safe lens
  rw [h] at this
  simpa [Inv] using this

end NgtcpRV.VecLenVarint
