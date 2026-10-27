/-!
Timer-elapsed determination (ngtcp2_conn timers).

ngtcp2 schedules timers (loss, PTO, idle, keep-alive, path-validation) as a
deadline `base + timeout`, and a timer has fired once the current time `ts`
reaches it.  Since time is monotone, a timer that has fired stays fired — the
timer logic never "un-fires".  We prove the elapsed predicate and its
monotonicity in `ts`.
-/
namespace NgtcpRV.ConnTimer

/-- A timer with deadline `base + timeout` has elapsed at time `ts`. -/
def elapsed (base timeout ts : Nat) : Bool := decide (base + timeout ≤ ts)

theorem elapsed_iff (base timeout ts : Nat) :
    elapsed base timeout ts = true ↔ base + timeout ≤ ts := by unfold elapsed; simp

/-- **Monotone in time**: once a timer has fired, it stays fired as time advances. -/
theorem elapsed_monotone (base timeout ts1 ts2 : Nat) (h : ts1 ≤ ts2)
    (he : elapsed base timeout ts1 = true) : elapsed base timeout ts2 = true := by
  rw [elapsed_iff] at he ⊢; omega

/-- A longer timeout fires no earlier (for the same base/time). -/
theorem longer_timeout_later (base t1 t2 ts : Nat) (h : t1 ≤ t2)
    (he : elapsed base t2 ts = true) : elapsed base t1 ts = true := by
  rw [elapsed_iff] at he ⊢; omega

end NgtcpRV.ConnTimer
