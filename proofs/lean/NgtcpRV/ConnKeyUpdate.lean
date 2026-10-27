/-!
Key-update STATE-MACHINE invariant (conn.c).

QUIC key update must be one-at-a-time: an endpoint may not start a new key update
until the previous one is confirmed (RFC 9001 §6).  ngtcp2 enforces this with the
NGTCP2_CONN_FLAG_KEY_UPDATE_NOT_CONFIRMED flag: `conn_rotate_keys` /
`conn_initiate_key_update` are guarded by `!(flags & NOT_CONFIRMED)`, and
`conn_handle_unconfirmed_key_update_from_remote` clears it on confirmation.  We
model the number of key updates awaiting confirmation and prove it never exceeds
one, for ANY sequence of (guarded) rotations and confirmations — so a second
rotation can never begin while one is pending (which would risk key/nonce
confusion).  By induction.
-/
namespace NgtcpRV.ConnKeyUpdate

/-- Number of key updates currently awaiting confirmation (0 or 1). -/
structure KuState where
  pending : Nat

/-- The invariant: at most one key update is in flight. -/
def KuInv (s : KuState) : Prop := s.pending ≤ 1

/-- Rotate keys — guarded exactly as `conn_rotate_keys` / `initiate_key_update`:
only allowed when nothing is pending (`!(flags & NOT_CONFIRMED)`); it then marks
an update pending.  A rotation attempted while one is pending is rejected. -/
def rotate (s : KuState) : KuState :=
  if s.pending = 0 then { pending := 1 } else s

/-- Confirm the in-flight update (clears NOT_CONFIRMED). -/
def confirm (_s : KuState) : KuState := { pending := 0 }

theorem rotate_inv (s : KuState) (h : KuInv s) : KuInv (rotate s) := by
  unfold KuInv rotate
  split
  · simp
  · exact h

theorem confirm_inv (s : KuState) (_h : KuInv s) : KuInv (confirm s) := by
  unfold KuInv confirm; simp

/-- A key-update event. -/
inductive Op where
  | rotate
  | confirm

def apply (s : KuState) : Op → KuState
  | .rotate  => rotate s
  | .confirm => confirm s

/-- **Key-update safety (whole state machine)**: from a valid state, ANY sequence
of rotations and confirmations keeps at most one key update in flight — ngtcp2
never starts a second key update while one is still unconfirmed, for any history.
By induction. -/
theorem seq_inv (ops : List Op) (s : KuState) (h : KuInv s) :
    KuInv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o with
    | rotate  => exact rotate_inv s h
    | confirm => exact confirm_inv s h

/-- Corollary: a rotation only ever starts from the confirmed state — if a
rotation changed the state, there was nothing pending before it. -/
theorem rotate_only_when_confirmed (s : KuState) (h : rotate s ≠ s) : s.pending = 0 := by
  unfold rotate at h; split at h
  · assumption
  · exact absurd rfl h

end NgtcpRV.ConnKeyUpdate
