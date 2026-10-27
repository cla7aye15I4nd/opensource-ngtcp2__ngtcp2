/-!
DATA_BLOCKED / STREAM_DATA_BLOCKED determination (conn.c, RFC 9000 §19.12-19.13).

An endpoint sends a (STREAM_)DATA_BLOCKED frame when it has data to send but is
stopped by flow control — i.e. its send offset has reached the advertised limit.
Given the maintained invariant `offset <= max_offset` (`ConnSendInv`), being
blocked is exactly `offset = max_offset`.  We prove the blocked predicate and that
it coincides with having zero remaining credit.
-/
namespace NgtcpRV.ConnBlocked

/-- Flow-control blocked: the send offset has reached the advertised maximum. -/
def blocked (offset maxOffset : Nat) : Bool := decide (maxOffset ≤ offset)

/-- With the invariant `offset <= max_offset`, blocked means exactly at the limit. -/
theorem blocked_iff_at_limit (offset maxOffset : Nat) (h : offset ≤ maxOffset) :
    blocked offset maxOffset = true ↔ offset = maxOffset := by
  unfold blocked; simp only [decide_eq_true_eq]; omega

/-- Blocked iff there is no remaining flow-control credit. -/
theorem blocked_iff_no_credit (offset maxOffset : Nat) (h : offset ≤ maxOffset) :
    blocked offset maxOffset = true ↔ maxOffset - offset = 0 := by
  unfold blocked; simp only [decide_eq_true_eq]; omega

end NgtcpRV.ConnBlocked
