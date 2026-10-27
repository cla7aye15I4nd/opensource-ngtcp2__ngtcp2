/-!
Slow-start phase determination (cc.c, RFC 9002 §7.3).

A connection is in slow start while `cwnd < ssthresh` and in congestion avoidance
once `cwnd >= ssthresh`.  A congestion event reduces `cwnd` and sets
`ssthresh = cwnd`, so immediately afterwards `cwnd = ssthresh` and the connection
is NOT in slow start — it enters congestion avoidance, as required (slow start is
not re-entered on loss).  We prove the phase predicate and this transition.
-/
namespace NgtcpRV.ConnSlowStart

/-- In slow start iff `cwnd < ssthresh`. -/
def inSlowStart (cwnd ssthresh : Nat) : Bool := decide (cwnd < ssthresh)

/-- A congestion event: reduce `cwnd` to `reduced` and set `ssthresh = reduced`. -/
def congestionEvent (reduced : Nat) : Nat × Nat := (reduced, reduced)

/-- **Exit slow start on loss**: after a congestion event, `cwnd = ssthresh`, so
the connection is in congestion avoidance (not slow start). -/
theorem not_slow_start_after_event (reduced : Nat) :
    inSlowStart (congestionEvent reduced).1 (congestionEvent reduced).2 = false := by
  unfold inSlowStart congestionEvent; simp

/-- Growing `cwnd` in slow start (toward `ssthresh`) eventually reaches congestion
avoidance: once `cwnd >= ssthresh` the phase flips. -/
theorem phase_boundary (cwnd ssthresh : Nat) :
    inSlowStart cwnd ssthresh = false ↔ ssthresh ≤ cwnd := by
  unfold inSlowStart; simp

end NgtcpRV.ConnSlowStart
