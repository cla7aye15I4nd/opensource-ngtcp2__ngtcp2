/-!
# conn.c key-update state machine: no re-rotation while an update is unconfirmed

This is the first STATEFUL conn.c subsystem modelled here (beyond the parsing
surface): the TLS 1.3 / QUIC key update procedure (RFC 9001 §6), driven by
`conn_prepare_key_update`, `conn_rotate_keys`, and
`conn_handle_unconfirmed_key_update_from_remote` in lib/ngtcp2_conn.c.

State is three booleans on `conn->flags` / `conn->crypto.key_update`:
  * `phase`        — the current key-phase bit (`NGTCP2_CRYPTO_KM_FLAG_KEY_PHASE_ONE`);
  * `notConfirmed` — `NGTCP2_CONN_FLAG_KEY_UPDATE_NOT_CONFIRMED`: an update is in flight;
  * `hasNewKeys`   — `crypto.key_update.new_rx_ckm/new_tx_ckm` installed, awaiting rotation;
plus `initiator` (`NGTCP2_CONN_FLAG_KEY_UPDATE_INITIATOR`).

The safety-critical property (preventing key confusion / nonce reuse) is that the
endpoint can NEVER rotate to a third key while the previous update is still
unconfirmed.  The code enforces it structurally: `conn_prepare_key_update` returns
early — installing NO new keys — whenever `NOT_CONFIRMED` is set (line 8820), and
`conn_rotate_keys` only acts when new keys are present.  So the invariant
`notConfirmed → ¬hasNewKeys` holds, and hence `rotate` is a no-op while unconfirmed.
Proved by induction over arbitrary operation sequences.
-/
namespace NgtcpRV.KeyUpdateSM

structure St where
  phase : Bool
  notConfirmed : Bool
  hasNewKeys : Bool
  initiator : Bool

inductive Op
  | prepare              -- conn_prepare_key_update: install new keys (unless blocked)
  | rotate (init : Bool) -- conn_rotate_keys: current←new, mark unconfirmed
  | confirm              -- key update confirmed: clear NOT_CONFIRMED

/-- One operation, faithful to the C control flow. -/
def apply (s : St) : Op → St
  | .prepare =>
      -- early return (no keys installed) if an update is unconfirmed or keys already staged
      if s.notConfirmed || s.hasNewKeys then s
      else { s with hasNewKeys := true }
  | .rotate init =>
      -- asserts new keys present; flips phase, consumes staged keys, marks unconfirmed
      if s.hasNewKeys then
        { phase := !s.phase, notConfirmed := true, hasNewKeys := false, initiator := init }
      else s
  | .confirm =>
      if s.notConfirmed then { s with notConfirmed := false } else s

def run (s0 : St) (ops : List Op) : St := ops.foldl apply s0

/-- Core invariant: while an update is unconfirmed, no new keys are staged — so a
second rotation cannot happen until the first is confirmed. -/
def Inv (s : St) : Prop := s.notConfirmed = true → s.hasNewKeys = false

/-- Every operation preserves the invariant. -/
theorem apply_preserves (s : St) (op : Op) (h : Inv s) : Inv (apply s op) := by
  cases op with
  | prepare =>
      simp only [apply, Inv]
      by_cases hc : s.notConfirmed || s.hasNewKeys
      · simp only [hc, if_true]; exact h
      · simp only [hc, if_false]
        intro hnc
        -- hc false ⇒ notConfirmed = false, contradicting hnc after the update keeps notConfirmed
        simp only [Bool.or_eq_true, not_or] at hc
        simp [hc.1] at hnc
  | rotate init =>
      simp only [apply, Inv]
      by_cases hk : s.hasNewKeys
      · simp [hk]
      · simp only [hk, if_false]; exact h
  | confirm =>
      simp only [apply, Inv]
      by_cases hnc : s.notConfirmed
      · simp [hnc]
      · simp only [hnc, if_false]; exact h

/-- **Main result**: from any state satisfying the invariant, the invariant holds
after every finite sequence of key-update operations. -/
theorem run_inv (s0 : St) (ops : List Op) (h : Inv s0) : Inv (run s0 ops) := by
  unfold run
  induction ops generalizing s0 with
  | nil => simpa using h
  | cons op ops ih =>
    simp only [List.foldl_cons]
    exact ih (apply s0 op) (apply_preserves s0 op h)

/-- **Headline safety property**: while an update is unconfirmed, `rotate` is a
no-op — the endpoint cannot install a third key before confirming the second.
This is exactly the anti-key-confusion guarantee of RFC 9001 §6. -/
theorem no_rotate_while_unconfirmed (s : St) (h : Inv s)
    (hnc : s.notConfirmed = true) (init : Bool) : apply s (.rotate init) = s := by
  have hk : s.hasNewKeys = false := h hnc
  simp [apply, hk]

/-- Each actual rotation flips the key-phase bit (phase alternation). -/
theorem rotate_flips_phase (s : St) (init : Bool) (hk : s.hasNewKeys = true) :
    (apply s (.rotate init)).phase = !s.phase := by
  simp only [apply, hk, if_true]

/-- The initial connection state (no update in flight) satisfies the invariant. -/
theorem init_inv : Inv ⟨false, false, false, false⟩ := by
  intro h; simp at h

end NgtcpRV.KeyUpdateSM
