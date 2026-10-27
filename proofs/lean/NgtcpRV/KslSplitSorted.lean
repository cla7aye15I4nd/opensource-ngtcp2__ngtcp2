/-!
ksl node-split SEMANTIC invariant (ngtcp2_ksl.c `ksl_split_blk`).

`KslSplit` proves the split's memcpy/memmove arithmetic stays in bounds.  This
module proves the *semantic* B-tree invariant the split must preserve: a block's
keys are kept sorted, and splitting a sorted block at any position yields a sorted
left block and a sorted right block whose keys are all greater-or-equal — so the
separator key (max of left) correctly routes searches, and the within-block
search (`KslSearch`) precondition (sorted keys) still holds after a split.
-/
namespace NgtcpRV.KslSplitSorted

/-- A block's keys are sorted (non-decreasing). -/
def Sorted (l : List (BitVec 64)) : Prop := l.Pairwise (· ≤ ·)

/-- The left block after a split (`blk->n - rblk->n` keys) stays sorted. -/
theorem take_sorted (l : List (BitVec 64)) (k : Nat) (h : Sorted l) :
    Sorted (l.take k) :=
  h.sublist (l.take_sublist k)

/-- The right block (`rblk->n` keys) stays sorted. -/
theorem drop_sorted (l : List (BitVec 64)) (k : Nat) (h : Sorted l) :
    Sorted (l.drop k) :=
  h.sublist (l.drop_sublist k)

/-- No key is lost across the split: left ++ right = original. -/
theorem split_recovers (l : List (BitVec 64)) (k : Nat) :
    l.take k ++ l.drop k = l := l.take_append_drop k

/-- **Separator ordering**: every key in the left block is `<=` every key in the
right block — so the B-tree routing key (max of the left) correctly separates the
two, and a lower-bound search still lands in the right subtree. -/
theorem split_separator (l : List (BitVec 64)) (k : Nat) (h : Sorted l) :
    ∀ x ∈ l.take k, ∀ y ∈ l.drop k, x ≤ y := by
  have hs : Sorted (l.take k ++ l.drop k) := by rw [l.take_append_drop]; exact h
  unfold Sorted at hs
  rw [List.pairwise_append] at hs
  exact hs.2.2

end NgtcpRV.KslSplitSorted
