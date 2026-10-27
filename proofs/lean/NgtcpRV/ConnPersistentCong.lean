import NgtcpRV.ConnCongestion
/-!
Persistent-congestion detection (cc.c, RFC 9002 §7.6).

If every packet in a span longer than `persistent_congestion_duration` is lost,
the sender declares persistent congestion and collapses the congestion window to
the minimum (`cwnd = min_cwnd`).  We model the detection threshold and prove the
collapse still respects the floor (via `ConnCongestion.reset_inv`).
-/
namespace NgtcpRV.ConnPersistentCong
open NgtcpRV.ConnCongestion

/-- Persistent congestion is declared when the all-lost span reaches the duration. -/
def persistentCongestion (lossSpan pcDuration : Nat) : Bool := decide (pcDuration ≤ lossSpan)

theorem pc_iff (lossSpan pcDuration : Nat) :
    persistentCongestion lossSpan pcDuration = true ↔ pcDuration ≤ lossSpan := by
  unfold persistentCongestion; simp

/-- **Collapse respects the floor**: resetting the window to `min_cwnd` on
persistent congestion keeps `min_cwnd <= cwnd` (the window equals the floor, not
below it). -/
theorem pc_collapse_respects_floor (s : CcState) (h : CcInv s) : CcInv (reset s) :=
  reset_inv s h

end NgtcpRV.ConnPersistentCong
