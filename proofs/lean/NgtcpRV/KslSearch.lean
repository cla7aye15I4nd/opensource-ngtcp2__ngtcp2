/-!
ngtcp2 ksl within-block search, proved for ALL block sizes by induction.

The C loop (ngtcp2_ksl_search_def):
  for (i = 0; i < blk->n && COMPAR(key[i], target); ++i) ;  return i;
scans the sorted keys of a block and returns the first index where the
comparator is false.  CBMC can only unroll it to a fixed n (=32); here the
block is a `List K`, the scan a recursive `search`, and every property holds
for every length.
-/
namespace NgtcpRV.KslSearch
variable {K : Type}

/-- The scan: first index where `lt` fails (or the whole length). Exactly the C loop. -/
def search (lt : K → Bool) : List K → Nat
  | [] => 0
  | x :: xs => if lt x then search lt xs + 1 else 0

/-- SPATIAL SAFETY: the returned index never exceeds `blk->n`, so every key the
loop touches (`key[0..i)`) lies inside the block. -/
theorem search_le (lt : K → Bool) (ks : List K) : search lt ks ≤ ks.length := by
  induction ks with
  | nil => simp [search]
  | cons x xs ih =>
    simp only [search, List.length_cons]
    by_cases h : lt x <;> simp [h] <;> omega

/-- CORRECTNESS 1: every key strictly before the result satisfies the comparator
(the loop only advanced past keys for which COMPAR held). -/
theorem search_all_lt (lt : K → Bool) (ks : List K) (j : Nat)
    (hj : j < search lt ks) : lt (ks.get ⟨j, by have := search_le lt ks; omega⟩) = true := by
  induction ks generalizing j with
  | nil => simp [search] at hj
  | cons x xs ih =>
    simp only [search] at hj
    by_cases h : lt x
    · simp only [h, if_true] at hj
      cases j with
      | zero => simpa using h
      | succ k => simpa using ih k (by omega)
    · simp [h] at hj

/-- CORRECTNESS 2 (lower bound): if the scan stopped before the end, the key at
the stop index fails the comparator — the defining property of the returned index. -/
theorem search_stop (lt : K → Bool) (ks : List K)
    (hlt : search lt ks < ks.length) :
    lt (ks.get ⟨search lt ks, hlt⟩) = false := by
  induction ks with
  | nil => simp [search] at hlt
  | cons x xs ih =>
    simp only [search] at hlt ⊢
    by_cases h : lt x
    · simp only [h, if_true] at hlt ⊢
      simpa using ih (by simpa using hlt)
    · simp [h]

end NgtcpRV.KslSearch

namespace NgtcpRV.KslSearch
/-- CAPSTONE for the concrete `uint64_less` comparator (`ngtcp2_ksl_uint64_less`),
keys as `BitVec 64`: the returned index `i` is a genuine lower bound — every key
before `i` is `< target`, and the key at `i` (if the scan stopped inside the
block) is `≥ target`. For a sorted block this is the unique insertion point.
Proved for EVERY block size. -/
theorem uint64_lower_bound (target : BitVec 64) (ks : List (BitVec 64)) :
    let lt := fun k => decide (k < target)
    (∀ j (hj : j < search lt ks),
        ks.get ⟨j, by have := search_le lt ks; omega⟩ < target)
    ∧ ∀ (h : search lt ks < ks.length), ¬ (ks.get ⟨search lt ks, h⟩ < target) := by
  intro lt
  refine ⟨fun j hj => ?_, fun h => ?_⟩
  · have := search_all_lt lt ks j hj
    exact of_decide_eq_true this
  · have := search_stop lt ks h
    exact of_decide_eq_false this
end NgtcpRV.KslSearch
