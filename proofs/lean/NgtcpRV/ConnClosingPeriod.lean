/-!
Closing/draining period (conn.c, RFC 9000 §10.2).

After sending or receiving CONNECTION_CLOSE, an endpoint remains in the closing
(or draining) state for three times the PTO, so that late or retransmitted packets
are handled gracefully before the connection state is discarded.  We prove the
closing period is `3 * PTO` — positive (so the state is retained) and at least the
PTO.
-/
namespace NgtcpRV.ConnClosingPeriod

/-- The closing/draining period. -/
def closingPeriod (pto : Nat) : Nat := 3 * pto

theorem closing_positive (pto : Nat) (h : 0 < pto) : 0 < closingPeriod pto := by
  unfold closingPeriod; omega

/-- The closing period is at least the PTO (late packets within one PTO are
covered). -/
theorem closing_ge_pto (pto : Nat) : pto ≤ closingPeriod pto := by
  unfold closingPeriod; omega

end NgtcpRV.ConnClosingPeriod
