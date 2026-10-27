/-!
ACK-delay scaling bound (conn.c `assign_recved_ack_delay_unscaled`).

A received ACK frame carries a (peer-controlled) `ack_delay`, scaled by
`exp = (1 << ack_delay_exponent) * MICROSECONDS` to nanoseconds.  To stop a
malicious peer from inflating the RTT estimate (or overflowing the multiply),
ngtcp2 clamps: `if (ack_delay > max_ack_delay / exp) use max_ack_delay; else
ack_delay * exp`.  We prove the non-clamped product is always `<= max_ack_delay`,
so the unscaled delay is bounded regardless of the peer's value — no overflow and
no RTT manipulation.
-/
namespace NgtcpRV.ConnAckDelay

/-- **Scaled ACK delay is bounded**: when the guard `ack_delay <= max_ack_delay /
exp` holds (the non-clamped branch), the product `ack_delay * exp` does not exceed
`max_ack_delay` — hence no overflow and a bounded RTT contribution. -/
theorem ack_delay_bounded (ackDelay exp maxDelay : Nat) (hexp : 0 < exp)
    (h : ackDelay ≤ maxDelay / exp) :
    ackDelay * exp ≤ maxDelay := by
  calc ackDelay * exp ≤ (maxDelay / exp) * exp := Nat.mul_le_mul_right exp h
    _ ≤ maxDelay := Nat.div_mul_le_self maxDelay exp

/-- The clamped branch is trivially bounded (`= max_ack_delay`), so the result is
`<= max_ack_delay` on every path. -/
theorem ack_delay_unscaled_bounded (ackDelay exp maxDelay : Nat) (hexp : 0 < exp) :
    (if maxDelay / exp < ackDelay then maxDelay else ackDelay * exp) ≤ maxDelay := by
  split
  · exact Nat.le_refl _
  · rename_i hle; exact ack_delay_bounded ackDelay exp maxDelay hexp (by omega)

end NgtcpRV.ConnAckDelay
