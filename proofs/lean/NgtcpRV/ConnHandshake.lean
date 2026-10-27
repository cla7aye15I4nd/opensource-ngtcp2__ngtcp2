/-!
Handshake-progression STATE-MACHINE invariant (conn.c).

The handshake lifecycle flags are set-only (monotone) and ordered: an endpoint
confirms the handshake only after completing it.  A server sets COMPLETED and
CONFIRMED together (`ngtcp2_conn_tls_handshake_completed`); a client sets
CONFIRMED later, in the post-handshake state (guarded by
`conn->state == NGTCP2_CS_POST_HANDSHAKE`).  Either way the invariant
`confirmed ⇒ completed` holds — ngtcp2 never treats the handshake as confirmed
while it is not yet complete (which would enable 1-RTT / key-update logic
prematurely).  Proved across ANY transition history, by induction.
-/
namespace NgtcpRV.ConnHandshake

/-- Handshake lifecycle flags. -/
structure HsState where
  completed : Bool
  confirmed : Bool

/-- Ordering invariant: confirmation implies completion. -/
def HsInv (s : HsState) : Prop := s.confirmed = true → s.completed = true

/-- Client/library: mark the handshake completed. -/
def complete (s : HsState) : HsState := { s with completed := true }
/-- Server: completion also confirms (tls_handshake_completed on the server). -/
def completeServer (_s : HsState) : HsState := { completed := true, confirmed := true }
/-- Client: confirm — only reachable after completion (post-handshake state). -/
def confirm (s : HsState) : HsState :=
  if s.completed then { s with confirmed := true } else s

/-- A handshake-progression event. -/
inductive Op where
  | complete
  | completeServer
  | confirm

def apply (s : HsState) : Op → HsState
  | .complete       => complete s
  | .completeServer => completeServer s
  | .confirm        => confirm s

theorem apply_inv (s : HsState) (o : Op) (h : HsInv s) : HsInv (apply s o) := by
  cases o with
  | complete => simp [apply, HsInv, complete]
  | completeServer => simp [apply, HsInv, completeServer]
  | confirm =>
    simp only [apply, confirm, HsInv]
    split
    · rename_i hc; intro _; exact hc
    · exact h

/-- **Handshake ordering (whole state machine)**: from a valid state, ANY sequence
of progression events keeps `confirmed ⇒ completed` — ngtcp2 never marks the
handshake confirmed before it is complete, for any history.  By induction. -/
theorem seq_inv (ops : List Op) (s : HsState) (h : HsInv s) :
    HsInv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih => exact ih _ (apply_inv s o h)

/-- Monotonicity: once completed, always completed (the flag is never cleared). -/
theorem seq_monotone_completed (ops : List Op) (s : HsState) (h : s.completed = true) :
    (ops.foldl apply s).completed = true := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o with
    | complete => simp [apply, complete]
    | completeServer => simp [apply, completeServer]
    | confirm =>
      simp only [apply, confirm]
      split
      · rename_i hc; exact hc
      · exact h

end NgtcpRV.ConnHandshake
