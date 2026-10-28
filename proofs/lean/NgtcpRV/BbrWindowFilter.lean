/-!
# conn.c windowed max-filter `ngtcp2_wf` (lib/ngtcp2_wf.c)

BBR tracks max bandwidth / extra-acked with a Kathleen-Nichols windowed max filter of
three samples kept in descending value order; `ngtcp2_wf_get_best` returns
`samples[0].value` (the maximum).  The value-maintenance core of `ngtcp2_wf_update`
is:

```c
  if (samples[0].value <= value /* or expired */) { samples[0]=samples[1]=samples[2]=s; return; }
  if (samples[1].value <= value) samples[1]=samples[2]=s;
  else if (samples[2].value <= value) samples[2]=s;
```

We model the three sample values and prove the descending-order invariant
`v0 >= v1 >= v2` is preserved by this update, that `get_best = v0` is the maximum of
the three, and that the value-insert never lowers the best (aging is the separate
time-window logic).
-/
namespace NgtcpRV.BbrWindowFilter

/-- The three sample values (`samples[0..2].value`). -/
structure Wf where
  v0 : Nat
  v1 : Nat
  v2 : Nat

/-- Samples are kept in descending value order. -/
def Ordered (w : Wf) : Prop := w.v1 ≤ w.v0 ∧ w.v2 ≤ w.v1

/-- `ngtcp2_wf_get_best`. -/
def getBest (w : Wf) : Nat := w.v0

/-- The value-maintenance part of `ngtcp2_wf_update`. -/
def insert (w : Wf) (value : Nat) : Wf :=
  if w.v0 ≤ value then ⟨value, value, value⟩
  else if w.v1 ≤ value then ⟨w.v0, value, value⟩
  else if w.v2 ≤ value then ⟨w.v0, w.v1, value⟩
  else w

/-- `get_best` is the maximum of the three samples. -/
theorem best_is_max (w : Wf) (h : Ordered w) : w.v1 ≤ getBest w ∧ w.v2 ≤ getBest w := by
  unfold Ordered at h; unfold getBest; omega

/-- **Ordering preserved**: the value update keeps the samples in descending order. -/
theorem insert_ordered (w : Wf) (value : Nat) (h : Ordered w) : Ordered (insert w value) := by
  unfold Ordered at h ⊢; unfold insert
  by_cases h0 : w.v0 ≤ value
  · rw [if_pos h0]; dsimp only; omega
  · rw [if_neg h0]
    by_cases h1 : w.v1 ≤ value
    · rw [if_pos h1]; dsimp only; omega
    · rw [if_neg h1]
      by_cases h2 : w.v2 ≤ value
      · rw [if_pos h2]; dsimp only; omega
      · rw [if_neg h2]; omega

/-- A new value at least the current best becomes the new best. -/
theorem insert_new_max (w : Wf) (value : Nat) (h : w.v0 ≤ value) :
    getBest (insert w value) = value := by
  unfold getBest insert; rw [if_pos h]

/-- **Best never decreases** under the value update (only time-window aging can drop it). -/
theorem insert_best_nondecreasing (w : Wf) (value : Nat) : getBest w ≤ getBest (insert w value) := by
  unfold getBest insert
  by_cases h0 : w.v0 ≤ value
  · rw [if_pos h0]; dsimp only; omega
  · rw [if_neg h0]
    by_cases h1 : w.v1 ≤ value
    · rw [if_pos h1]; dsimp only; omega
    · rw [if_neg h1]
      by_cases h2 : w.v2 ≤ value
      · rw [if_pos h2]; dsimp only; omega
      · rw [if_neg h2]; omega

end NgtcpRV.BbrWindowFilter
