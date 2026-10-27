/-!
Idle-timeout negotiation (conn.c, RFC 9000 §10.1).

The effective idle timeout is the minimum of the two endpoints' advertised
`max_idle_timeout` values, where 0 means "no limit".  ngtcp2 selects:
`if (rmt == 0 || (lcl && lcl < rmt)) use lcl; else use rmt;`.
We prove the selected timeout never exceeds either party's nonzero advertised
value — the connection is never kept alive longer than BOTH endpoints allow.
-/
namespace NgtcpRV.ConnIdleTimeout

/-- The selected effective idle timeout (0 = no limit on that side). -/
def effective (lcl rmt : Nat) : Nat :=
  if rmt = 0 ∨ (lcl ≠ 0 ∧ lcl < rmt) then lcl else rmt

/-- **Within the lcl limit**: if the lcl endpoint set a finite idle timeout,
the effective timeout does not exceed it. -/
theorem effective_le_local (lcl rmt : Nat) (h : lcl ≠ 0) :
    effective lcl rmt ≤ lcl := by
  unfold effective; split <;> omega

/-- **Within the rmt limit**: if the peer set a finite idle timeout, the
effective timeout does not exceed it. -/
theorem effective_le_remote (lcl rmt : Nat) (h : rmt ≠ 0) :
    effective lcl rmt ≤ rmt := by
  unfold effective; split <;> omega

/-- The effective timeout is one of the two advertised values. -/
theorem effective_mem (lcl rmt : Nat) :
    effective lcl rmt = lcl ∨ effective lcl rmt = rmt := by
  unfold effective; split
  · exact Or.inl rfl
  · exact Or.inr rfl

end NgtcpRV.ConnIdleTimeout
