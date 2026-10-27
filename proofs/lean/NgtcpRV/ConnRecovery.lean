/-!
Congestion recovery period (cc.c / rtb.c, RFC 9002 §7.3.2).

After a congestion event the window is reduced once and a recovery period begins
at `congestion_recovery_start_ts`.  A later loss of a packet that was SENT BEFORE
the recovery started must NOT trigger another reduction — otherwise one burst of
losses could collapse the window repeatedly.  ngtcp2 guards with
`in_congestion_recovery(sent_time) = sent_time <= recovery_start_ts`.  We prove
the guard is correct and that entering recovery only moves the start forward, so
packets already in flight at the event are covered.
-/
namespace NgtcpRV.ConnRecovery

/-- A packet sent at `sentTime` is within the current recovery period. -/
def inRecovery (sentTime recoveryStart : Nat) : Bool := decide (sentTime ≤ recoveryStart)

/-- A new congestion event moves the recovery start forward (to the event time),
never backward. -/
def enterRecovery (recoveryStart eventTime : Nat) : Nat := max recoveryStart eventTime

/-- **No double reduction**: a packet sent at or before the recovery start is in
recovery, so its loss does not start a new congestion event. -/
theorem no_double_reduction (sentTime recoveryStart : Nat) (h : sentTime ≤ recoveryStart) :
    inRecovery sentTime recoveryStart = true := by
  unfold inRecovery; simpa using h

/-- Entering recovery only advances the start; packets already covered stay
covered. -/
theorem recovery_start_monotone (recoveryStart eventTime : Nat) :
    recoveryStart ≤ enterRecovery recoveryStart eventTime := by
  unfold enterRecovery; omega

theorem still_in_recovery (sentTime recoveryStart eventTime : Nat)
    (h : inRecovery sentTime recoveryStart = true) :
    inRecovery sentTime (enterRecovery recoveryStart eventTime) = true := by
  unfold inRecovery enterRecovery at *; simp only [decide_eq_true_eq] at *; omega

end NgtcpRV.ConnRecovery
