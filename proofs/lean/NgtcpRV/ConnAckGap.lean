/-!
ACK-frame gap encoding (conn.c / pkt.c, RFC 9000 §19.3).

An ACK frame lists acknowledged packet-number ranges in descending order; between
two consecutive ranges the "Gap" field encodes the number of unacknowledged
packets as `gap = smallest_of_this_range - largest_of_next_range - 2`.  Because
the ranges are disjoint and separated (`largest_of_next + 2 <= smallest_of_this`),
the subtraction never underflows, and the decoder recovers the next range's
largest exactly.  We prove both.
-/
namespace NgtcpRV.ConnAckGap

/-- The encoded Gap between a range with smallest `lo` and the next range with
largest `nextHi`. -/
def gap (lo nextHi : Nat) : Nat := lo - nextHi - 2

/-- **No underflow**: for disjoint, separated ranges (`nextHi + 2 <= lo`) the gap
is exact — `lo - (gap + 2) = nextHi`, so re-adding recovers `lo`. -/
theorem gap_exact (lo nextHi : Nat) (h : nextHi + 2 ≤ lo) :
    gap lo nextHi + nextHi + 2 = lo := by
  unfold gap; omega

/-- **Decode recovers the boundary**: from `lo` and the encoded gap, the next
range's largest packet number is recovered exactly. -/
theorem gap_decode (lo nextHi : Nat) (h : nextHi + 2 ≤ lo) :
    lo - (gap lo nextHi + 2) = nextHi := by
  unfold gap; omega

end NgtcpRV.ConnAckGap
