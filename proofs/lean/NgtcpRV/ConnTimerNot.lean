import NgtcpRV.ConnTimer
/-!
Timer not-yet-elapsed (conn.c `ngtcp2_tstamp_not_elapsed`).

Several guards test whether a timer has NOT yet fired (e.g. the 3*PTO wait before a
key update).  This is the exact negation of `ConnTimer.elapsed`: not elapsed iff
`ts < base + timeout`.  We prove the duality and that "not elapsed" is downward
closed in time (if not elapsed at a later time, it was not elapsed earlier).
-/
namespace NgtcpRV.ConnTimerNot
open NgtcpRV.ConnTimer

/-- A timer has not yet fired at time `ts`. -/
def notElapsed (base timeout ts : Nat) : Bool := decide (ts < base + timeout)

/-- Not elapsed iff the current time is before the deadline (negation of `elapsed`). -/
theorem notElapsed_iff (base timeout ts : Nat) :
    notElapsed base timeout ts = true ↔ ts < base + timeout := by
  unfold notElapsed; simp

/-- `notElapsed` and `elapsed` are mutually exclusive. -/
theorem not_both (base timeout ts : Nat) :
    ¬ (notElapsed base timeout ts = true ∧ elapsed base timeout ts = true) := by
  rw [notElapsed_iff, elapsed_iff]; omega

/-- Downward closed in time: not elapsed later implies not elapsed earlier. -/
theorem notElapsed_earlier (base timeout ts1 ts2 : Nat) (h : ts1 ≤ ts2)
    (hn : notElapsed base timeout ts2 = true) : notElapsed base timeout ts1 = true := by
  unfold notElapsed at *; simp only [decide_eq_true_eq] at *; omega

end NgtcpRV.ConnTimerNot
