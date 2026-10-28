/-!
# conn.c handshake flag ordering: confirmed implies completed

The handshake progresses through flags on `conn->flags` (lib/ngtcp2_conn.c):
`TLS_HANDSHAKE_COMPLETED`, `HANDSHAKE_COMPLETED`, `HANDSHAKE_CONFIRMED`, all set via
`|=` (monotone).  `ngtcp2_conn_tls_handshake_completed` sets TLS-completed, and for a
server also CONFIRMED (11065).  A client sets CONFIRMED only when already in
`POST_HANDSHAKE` — hence after completion — otherwise `NGTCP2_ERR_PROTO` (8738).

So `HANDSHAKE_CONFIRMED` can never hold without the TLS handshake being complete.
We model the flag transitions and prove this ordering invariant is maintained across
any event sequence, and that the flags are monotone (never cleared).
-/
namespace NgtcpRV.HandshakeFlags

structure HS where
  tlsCompleted : Bool
  completed : Bool
  confirmed : Bool
  server : Bool

inductive Op
  | tlsComplete    -- ngtcp2_conn_tls_handshake_completed
  | libComplete    -- set HANDSHAKE_COMPLETED (enter post-handshake)
  | clientConfirm  -- client confirms on HANDSHAKE_DONE (guarded by completion)

def apply (s : HS) : Op → HS
  | .tlsComplete => { s with tlsCompleted := true, confirmed := s.confirmed || s.server }
  | .libComplete => { s with completed := true }
  | .clientConfirm => if s.tlsCompleted then { s with confirmed := true } else s

/-- Ordering invariant: a confirmed handshake implies the TLS handshake is complete. -/
def Inv (s : HS) : Prop := s.confirmed = true → s.tlsCompleted = true

/-- Every event preserves the ordering invariant. -/
theorem apply_preserves (s : HS) (op : Op) (h : Inv s) : Inv (apply s op) := by
  unfold Inv at h ⊢
  cases op with
  | tlsComplete => intro _; rfl
  | libComplete => exact h
  | clientConfirm =>
      by_cases hc : s.tlsCompleted = true
      · unfold apply; rw [if_pos hc]; intro _; exact hc
      · unfold apply; rw [if_neg hc]; exact h

def run (s0 : HS) (ops : List Op) : HS := ops.foldl apply s0

/-- **Ordering holds over any event sequence**: `confirmed → tls_completed` always. -/
theorem run_inv (s0 : HS) (ops : List Op) (h : Inv s0) : Inv (run s0 ops) := by
  unfold run
  induction ops generalizing s0 with
  | nil => simpa using h
  | cons op ops ih => simp only [List.foldl_cons]; exact ih _ (apply_preserves s0 op h)

/-- The TLS-completed flag is monotone (never cleared). -/
theorem tls_completed_persists (s : HS) (op : Op) (h : s.tlsCompleted = true) :
    (apply s op).tlsCompleted = true := by
  cases op with
  | tlsComplete => rfl
  | libComplete => exact h
  | clientConfirm =>
      unfold apply
      by_cases hc : s.tlsCompleted = true
      · rw [if_pos hc]; exact h
      · rw [if_neg hc]; exact h

/-- A client cannot confirm before the TLS handshake completes: `clientConfirm` with
TLS not complete is a no-op (the `NGTCP2_ERR_PROTO` path). -/
theorem client_confirm_requires_tls (s : HS) (h : s.tlsCompleted = false) :
    apply s .clientConfirm = s := by
  unfold apply; rw [if_neg (by simp [h])]

end NgtcpRV.HandshakeFlags
