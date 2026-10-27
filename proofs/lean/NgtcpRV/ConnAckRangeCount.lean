/-!
ACK-range count bound (acktr.c, RFC 9000 §19.3).

An ACK frame holds its ranges in a fixed `NGTCP2_MAX_ACK_RANGES = 32`-element
array.  `ngtcp2_acktr_create_ack_frame` clamps the number of ranges with
`num_acks = ngtcp2_min(num_acks, NGTCP2_MAX_ACK_RANGES)`, so the range writes never
exceed the array.  We prove the clamp bounds the count at 32 and keeps every write
index in bounds.
-/
namespace NgtcpRV.ConnAckRangeCount

def MAX_ACK_RANGES : Nat := 32

/-- `ngtcp2_min(num_acks, NGTCP2_MAX_ACK_RANGES)`. -/
def clampedAcks (rawAcks : Nat) : Nat := min rawAcks MAX_ACK_RANGES

/-- The clamped range count never exceeds the array size. -/
theorem acks_bounded (rawAcks : Nat) : clampedAcks rawAcks ≤ 32 := by
  unfold clampedAcks MAX_ACK_RANGES; omega

/-- Every ACK-range write index stays within the 32-element array. -/
theorem ack_write_in_bounds (rawAcks i : Nat) (hi : i < clampedAcks rawAcks) : i < 32 := by
  unfold clampedAcks MAX_ACK_RANGES at hi; omega

end NgtcpRV.ConnAckRangeCount
