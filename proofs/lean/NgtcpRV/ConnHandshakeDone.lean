/-!
HANDSHAKE_DONE once (conn.c, RFC 9000 §19.20 / §7.3).

The server sends a single HANDSHAKE_DONE frame to signal handshake confirmation;
the client confirms the handshake on the first HANDSHAKE_DONE and ignores any
further ones.  ngtcp2 records this with a set-only flag.  We model it and prove
that once HANDSHAKE_DONE has been processed, no later one changes the state.
-/
namespace NgtcpRV.ConnHandshakeDone

structure S where
  done : Bool

/-- Process a received HANDSHAKE_DONE: confirm (set the flag) once. -/
def recvDone (s : S) : S := if s.done then s else { done := true }

def apply (s : S) : Unit → S := fun _ => recvDone s

/-- **At most once**: once HANDSHAKE_DONE is processed, it stays done across any
further HANDSHAKE_DONE events. -/
theorem done_stays (ops : List Unit) (s : S) (h : s.done = true) :
    (ops.foldl apply s).done = true := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih => refine ih _ ?_; unfold apply recvDone; simp [h]

/-- A HANDSHAKE_DONE is only processed from the not-yet-done state. -/
theorem done_only_once (s : S) (h : recvDone s ≠ s) : s.done = false := by
  unfold recvDone at h; split at h
  · exact absurd rfl h
  · rename_i hc; simpa using hc

end NgtcpRV.ConnHandshakeDone
