/-!
Active-DCID count bound (dcidtr.c, RFC 9000 §5.1.1).

An endpoint maintains at most `active_connection_id_limit` usable (not-yet-retired)
destination connection IDs supplied by the peer; a NEW_CONNECTION_ID that would
exceed it is a CONNECTION_ID_LIMIT_ERROR.  Combined with `ConnActiveCidLimit`
(limit >= 2), this keeps the active-DCID set bounded and non-empty.  We prove the
bound.
-/
namespace NgtcpRV.ConnActiveDcid

/-- The active-DCID count must not exceed the advertised limit. -/
def activeDcidOk (numActive limit : Nat) : Bool := decide (numActive ≤ limit)

theorem active_within_limit (numActive limit : Nat) (h : activeDcidOk numActive limit = true) :
    numActive ≤ limit := by unfold activeDcidOk at h; simpa using h

/-- Exceeding the limit is rejected. -/
theorem over_limit_rejected (numActive limit : Nat) (h : limit < numActive) :
    activeDcidOk numActive limit = false := by
  unfold activeDcidOk; simp; omega

end NgtcpRV.ConnActiveDcid
