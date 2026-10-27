/-!
Connection-level flow-control accounting (conn.c, RFC 9000 §4.1).

Connection-level flow control bounds the TOTAL data across all streams: the
connection's `tx.offset` is the sum of the per-stream sent amounts, and it must not
exceed the connection limit `tx.max_offset`.  We prove that if each stream's
contribution is accounted in the connection offset and the connection offset is
within its limit, then the total across all streams is within the connection
limit — so no single stream nor their sum can exceed connection-level credit.
-/
namespace NgtcpRV.ConnLevelFlow

/-- The total sent across all streams. -/
def totalSent (streamSent : List Nat) : Nat := streamSent.sum

/-- **Total within the connection limit**: if the connection offset equals the sum
of per-stream sends and is within the connection limit, the total is too. -/
theorem total_within_limit (streamSent : List Nat) (connOffset connMax : Nat)
    (hacct : connOffset = totalSent streamSent) (hlim : connOffset ≤ connMax) :
    totalSent streamSent ≤ connMax := by
  rw [← hacct]; exact hlim

/-- Each stream's contribution is at most the total (so no stream alone exceeds the
connection limit either). -/
theorem stream_le_total (streamSent : List Nat) (x : Nat) (hx : x ∈ streamSent) :
    x ≤ totalSent streamSent := by
  unfold totalSent
  induction streamSent with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · have := ih hx'; omega

end NgtcpRV.ConnLevelFlow
