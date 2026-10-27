/-!
STREAMS_BLOCKED determination (conn.c, RFC 9000 §19.14).

An endpoint that wants to open a stream but has reached the peer's `max_streams`
limit sends a STREAMS_BLOCKED frame.  Given the invariant `opened <= max_streams`
(`ConnStreamLimit`), being stream-blocked is exactly `opened = max_streams`.  We
prove the predicate.
-/
namespace NgtcpRV.ConnStreamsBlocked

/-- Stream-blocked: the opened count has reached the stream limit. -/
def streamsBlocked (opened maxStreams : Nat) : Bool := decide (maxStreams ≤ opened)

/-- With the invariant `opened <= max_streams`, blocked means exactly at the limit. -/
theorem streams_blocked_iff (opened maxStreams : Nat) (h : opened ≤ maxStreams) :
    streamsBlocked opened maxStreams = true ↔ opened = maxStreams := by
  unfold streamsBlocked; simp only [decide_eq_true_eq]; omega

/-- Blocked iff no stream credit remains. -/
theorem streams_blocked_iff_no_credit (opened maxStreams : Nat) (h : opened ≤ maxStreams) :
    streamsBlocked opened maxStreams = true ↔ maxStreams - opened = 0 := by
  unfold streamsBlocked; simp only [decide_eq_true_eq]; omega

end NgtcpRV.ConnStreamsBlocked
