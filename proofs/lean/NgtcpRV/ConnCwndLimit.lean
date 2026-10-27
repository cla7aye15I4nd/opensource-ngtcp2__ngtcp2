/-!
Congestion-window send limit (conn.c / cc.c, RFC 9002 §7).

An endpoint may only send while `bytes_in_flight < cwnd`; the amount it may send
is `cwnd - bytes_in_flight` (the available window).  We prove that sending the
available window never pushes `bytes_in_flight` past `cwnd` — congestion control is
respected, and the window is never over-committed.
-/
namespace NgtcpRV.ConnCwndLimit

/-- Bytes available to send without exceeding the congestion window. -/
def available (cwnd inFlight : Nat) : Nat := if inFlight < cwnd then cwnd - inFlight else 0

/-- **Window respected**: after sending the available amount, bytes in flight do
not exceed the congestion window. -/
theorem send_respects_cwnd (cwnd inFlight : Nat) (h : inFlight ≤ cwnd) :
    inFlight + available cwnd inFlight ≤ cwnd := by
  unfold available; split <;> omega

/-- The available window is zero exactly when the connection is cwnd-limited
(`bytes_in_flight >= cwnd`). -/
theorem cwnd_limited_iff (cwnd inFlight : Nat) :
    available cwnd inFlight = 0 ↔ cwnd ≤ inFlight := by
  unfold available; split <;> omega

end NgtcpRV.ConnCwndLimit
