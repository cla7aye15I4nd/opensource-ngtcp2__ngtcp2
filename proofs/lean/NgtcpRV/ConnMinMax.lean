/-!
ngtcp2_min / ngtcp2_max helper correctness (ngtcp2_macro.h).

`ngtcp2_min(a,b) = (a) < (b) ? (a) : (b)` and `ngtcp2_max(a,b) = (a) < (b) ?
(b) : (a)` are used pervasively (flow-control credits, UDP payload shaping, RTT
variance, padding, …).  We prove they compute the mathematical minimum and
maximum, so every `min`/`max`-based bound proved elsewhere is faithful to the C.
-/
namespace NgtcpRV.ConnMinMax

def ngtcp2_min (a b : Nat) : Nat := if a < b then a else b
def ngtcp2_max (a b : Nat) : Nat := if a < b then b else a

/-- `ngtcp2_min` is the minimum. -/
theorem ngtcp2_min_eq (a b : Nat) : ngtcp2_min a b = min a b := by
  unfold ngtcp2_min; split <;> omega

/-- `ngtcp2_max` is the maximum. -/
theorem ngtcp2_max_eq (a b : Nat) : ngtcp2_max a b = max a b := by
  unfold ngtcp2_max; split <;> omega

/-- Consequences used throughout: `min <= both`, `max >= both`. -/
theorem min_le (a b : Nat) : ngtcp2_min a b ≤ a ∧ ngtcp2_min a b ≤ b := by
  unfold ngtcp2_min; split <;> omega
theorem le_max (a b : Nat) : a ≤ ngtcp2_max a b ∧ b ≤ ngtcp2_max a b := by
  unfold ngtcp2_max; split <;> omega

end NgtcpRV.ConnMinMax
