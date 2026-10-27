/-!
max_ack_delay / ack_delay_exponent validation (transport_params.c, RFC 9000 §18.2).

`max_ack_delay` MUST be less than 2^14 (it is in milliseconds), and
`ack_delay_exponent` MUST be at most 20; larger values are
TRANSPORT_PARAMETER_ERROR.  These bounds keep the ACK-delay scaling well-behaved
(see `ConnAckDelay`).  We prove the two validations establish their bounds.
-/
namespace NgtcpRV.ConnMaxAckDelay

/-- `max_ack_delay < 2^14` and `ack_delay_exponent <= 20`. -/
def validAckDelay (maxAckDelay exponent : Nat) : Bool :=
  decide (maxAckDelay < 2 ^ 14 ∧ exponent ≤ 20)

/-- **Bounds established**: a validated `max_ack_delay` is `< 2^14` and a validated
`ack_delay_exponent` is `<= 20`, so `1 << exponent` is well-defined and the
ACK-delay scaling stays bounded. -/
theorem ack_delay_params_bounded (maxAckDelay exponent : Nat)
    (h : validAckDelay maxAckDelay exponent = true) :
    maxAckDelay < 2 ^ 14 ∧ exponent ≤ 20 ∧ exponent < 64 := by
  unfold validAckDelay at h
  simp only [decide_eq_true_eq] at h
  omega

end NgtcpRV.ConnMaxAckDelay
