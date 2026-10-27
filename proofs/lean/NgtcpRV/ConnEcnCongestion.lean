import NgtcpRV.ConnCongestion
/-!
ECN CE mark triggers congestion response (conn.c / cc.c, RFC 9002 §7.1).

When an ACK reports an increased ECN-CE count, ngtcp2 treats it like a loss: it
runs a congestion event, reducing the window (floored at `min_cwnd`).  We model the
CE-triggered reduction as `ConnCongestion.congEvent` and prove a CE increase
triggers it and that the reduced window still respects the floor.
-/
namespace NgtcpRV.ConnEcnCongestion
open NgtcpRV.ConnCongestion

/-- A CE-count increase indicates new congestion. -/
def ceTriggers (oldCE newCE : Nat) : Bool := decide (oldCE < newCE)

theorem ce_increase_triggers (oldCE newCE : Nat) (h : oldCE < newCE) :
    ceTriggers oldCE newCE = true := by unfold ceTriggers; simpa using h

/-- **CE congestion response is safe**: after a CE-triggered congestion event, the
window still satisfies `min_cwnd <= cwnd` (the floor from `ConnCongestion`), so ECN
congestion control never drives the window below the minimum. -/
theorem ce_congestion_respects_floor (s : CcState) (h : CcInv s) :
    CcInv (congEvent s) := congEvent_inv s h

end NgtcpRV.ConnEcnCongestion
