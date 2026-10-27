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

/-! ## Functional correctness: a sound AND complete overflow detector

`run_safe` above shows the loop never produces an out-of-range value.  The
stronger statements below pin down *exactly* what it computes, by relating it to
`nsum`, the TRUE unbounded sum of the lengths (a plain `ℕ`, so it never wraps).
Together they say the C function is a sound and complete overflow detector:
it returns the exact sum precisely when the sum fits in a varint, and `-1`
precisely when the sum would exceed `MAX`.  Both are proved by induction on the
list — statements that unrolling to a fixed bound cannot even express. -/

/-- The TRUE, unbounded sum of the vector lengths (plain `ℕ`, never wraps). -/
def nsum : List (BitVec 64) → Nat
  | [] => 0
  | x :: xs => x.toNat + nsum xs

/-- Once the loop has returned `-1`, it stays `-1`. -/
theorem foldl_none (xs : List (BitVec 64)) : xs.foldl step none = none := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [List.foldl_cons, step, ih]

/-- Generalized spec over an accumulator `a`: started at `a`, the loop returns
`some (a + Σlengths)` when that fits in a varint, and `-1` otherwise. -/
theorem foldl_spec (xs : List (BitVec 64)) :
    ∀ a : BitVec 64, a.toNat ≤ MAXV.toNat →
      xs.foldl step (some a) =
        if a.toNat + nsum xs ≤ MAXV.toNat
        then some (BitVec.ofNat 64 (a.toNat + nsum xs)) else none := by
  induction xs with
  | nil =>
    intro a ha
    simp only [List.foldl_nil, nsum, Nat.add_zero]
    rw [if_pos ha, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  | cons x xs ih =>
    intro a ha
    simp only [List.foldl_cons, step, nsum]
    by_cases hg : MAXV - a < x
    · rw [if_pos hg, foldl_none]
      have hx : MAXV.toNat - a.toNat < x.toNat := by bv_omega
      rw [if_neg (by omega)]
    · rw [if_neg hg]
      have hax : (a + x).toNat = a.toNat + x.toNat := by bv_omega
      have hle : (a + x).toNat ≤ MAXV.toNat := by bv_omega
      rw [ih (a + x) hle, hax, Nat.add_assoc]

theorem zero_le_max : (0#64).toNat ≤ MAXV.toNat := by
  show (0 : Nat) ≤ MAXV.toNat; exact Nat.zero_le _

/-- **SOUNDNESS**: if the loop returns a value `r`, then `r` is the exact true sum
of all the vector lengths, and that sum is a valid varint (`≤ MAX`) — no
wraparound and no spurious overflow report. -/
theorem run_sound (lens : List (BitVec 64)) (r : BitVec 64) (h : run lens = some r) :
    r.toNat = nsum lens ∧ nsum lens ≤ MAXV.toNat := by
  have hs := foldl_spec lens 0#64 zero_le_max
  unfold run at h
  rw [hs, (show (0#64).toNat = 0 from rfl), Nat.zero_add] at h
  by_cases hc : nsum lens ≤ MAXV.toNat
  · rw [if_pos hc] at h
    injection h with h; subst h
    refine ⟨?_, hc⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := MAXV.isLt; omega)]
  · rw [if_neg hc] at h; exact absurd h (by simp)

/-- **COMPLETENESS**: the loop returns `-1` (`none`) iff the true, unbounded sum of
the lengths would exceed `MAX` — the overflow check fires exactly when it must,
never early and never late. -/
theorem run_overflow_iff (lens : List (BitVec 64)) :
    run lens = none ↔ MAXV.toNat < nsum lens := by
  have hs := foldl_spec lens 0#64 zero_le_max
  unfold run
  rw [hs, (show (0#64).toNat = 0 from rfl), Nat.zero_add]
  by_cases hc : nsum lens ≤ MAXV.toNat
  · rw [if_pos hc]; exact ⟨fun h => absurd h (by simp), fun h => by omega⟩
  · rw [if_neg hc]; exact ⟨fun _ => by omega, fun _ => rfl⟩

end NgtcpRV.VecLenVarint
