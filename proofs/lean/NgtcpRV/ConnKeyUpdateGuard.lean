/-!
Key-update initiation guard (conn.c `conn_initiate_key_update`, RFC 9001 §6).

An endpoint may initiate a key update only after the handshake is CONFIRMED and
when no key update is already in flight.  This ties together `ConnHandshake`
(handshake must be confirmed) and `ConnKeyUpdate` (at most one update pending).
We prove the guard forbids a key update before the handshake is confirmed and
while one is pending.
-/
namespace NgtcpRV.ConnKeyUpdateGuard

/-- The `conn_initiate_key_update` guard: handshake confirmed AND nothing pending. -/
def canInitiate (hsConfirmed : Bool) (pending : Nat) : Bool :=
  hsConfirmed && decide (pending = 0)

/-- **Requires a confirmed handshake**: no key update can be initiated before the
handshake is confirmed. -/
theorem needs_handshake_confirmed (pending : Nat) : canInitiate false pending = false := by
  unfold canInitiate; simp

/-- **Requires no pending update**: no key update can be initiated while one is
already in flight (`pending != 0`). -/
theorem needs_no_pending (hsConfirmed : Bool) (pending : Nat) (h : pending ≠ 0) :
    canInitiate hsConfirmed pending = false := by
  unfold canInitiate; simp [h]

/-- When allowed, both conditions hold. -/
theorem initiate_sound (hsConfirmed : Bool) (pending : Nat) (h : canInitiate hsConfirmed pending = true) :
    hsConfirmed = true ∧ pending = 0 := by
  unfold canInitiate at h; simp_all

end NgtcpRV.ConnKeyUpdateGuard
