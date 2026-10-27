/-!
Retry-at-most-once (conn.c, RFC 9000 §8.1 / §17.2.5).

A server sends at most one Retry packet per connection attempt, and a client
accepts at most one Retry (a second Retry MUST be ignored).  ngtcp2 records that a
Retry has been sent/received with a flag that is only ever set.  We model the flag
and prove that once a Retry has occurred, no further Retry is processed across any
subsequent event history.
-/
namespace NgtcpRV.ConnRetryOnce

structure S where
  retryDone : Bool

/-- Mark a Retry as sent/received (set-only). -/
def doRetry (s : S) : S := { retryDone := true }

/-- A second Retry is a no-op once one has occurred (ignored). -/
def recvRetry (s : S) : S := if s.retryDone then s else doRetry s

/-- `recvRetry` never clears the flag. -/
def apply (s : S) : Unit → S := fun _ => recvRetry s

/-- **At most one Retry**: once a Retry has occurred, it stays done across any
number of further Retry events — a second Retry never re-triggers processing. -/
theorem retry_stays_done (ops : List Unit) (s : S) (h : s.retryDone = true) :
    (ops.foldl apply s).retryDone = true := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    unfold apply recvRetry; simp [h]

/-- A Retry is only processed (flag changes) from the not-yet-retried state. -/
theorem retry_only_once (s : S) (h : recvRetry s ≠ s) : s.retryDone = false := by
  unfold recvRetry at h; split at h
  · exact absurd rfl h
  · rename_i hc; simpa using hc

end NgtcpRV.ConnRetryOnce
