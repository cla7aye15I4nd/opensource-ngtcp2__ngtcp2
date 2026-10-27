/-!
Advertised flow-control limit monotonicity (conn.c, RFC 9000 §4.1).

An endpoint grows the flow-control limit it advertises (MAX_DATA /
MAX_STREAM_DATA) as data is consumed; it must never shrink an advertised limit
(the peer may already be relying on it).  ngtcp2 only ever raises
`rx.unsent_max_offset`.  We prove the advertised limit, after ANY sequence of
updates, is at least its starting value — a credit, once granted, is never
revoked.  By induction.
-/
namespace NgtcpRV.ConnMaxData

/-- Raise the advertised limit to `newLimit` (only if larger — never shrink). -/
def raise (cur newLimit : Nat) : Nat := max cur newLimit

/-- Fold a sequence of limit updates. -/
def advertise (cur : Nat) (updates : List Nat) : Nat := updates.foldl raise cur

/-- One update never lowers the advertised limit. -/
theorem raise_ge (cur newLimit : Nat) : cur ≤ raise cur newLimit := by
  unfold raise; omega

/-- **Monotone**: the advertised limit after any update sequence is at least the
starting value — granted credit is never revoked. -/
theorem advertise_ge (cur : Nat) (updates : List Nat) : cur ≤ advertise cur updates := by
  unfold advertise
  induction updates generalizing cur with
  | nil => simp
  | cons u us ih => exact Nat.le_trans (raise_ge cur u) (ih (raise cur u))

end NgtcpRV.ConnMaxData
