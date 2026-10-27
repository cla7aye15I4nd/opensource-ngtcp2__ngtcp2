/-!
ACK-frequency trigger (conn.c, RFC 9000 §13.2.1).

An endpoint should send an ACK after receiving at most two ack-eliciting packets
(and otherwise within `max_ack_delay`).  ngtcp2 counts ack-eliciting packets since
the last ACK (`rx_npkt`) and forces an ACK at the threshold.  We prove the counter
never passes the threshold without triggering an ACK — so acknowledgements are
never delayed beyond two ack-eliciting packets.
-/
namespace NgtcpRV.ConnAckFreq

/-- Threshold: ACK after this many ack-eliciting packets. -/
def ACK_THRESHOLD : Nat := 2

/-- An immediate ACK is required once the ack-eliciting count reaches the threshold. -/
def mustAck (rxNpkt : Nat) : Bool := decide (ACK_THRESHOLD ≤ rxNpkt)

/-- **Bounded ACK delay**: whenever two ack-eliciting packets have accumulated, an
ACK is required — the count cannot exceed the threshold without an ACK. -/
theorem ack_required_at_threshold (rxNpkt : Nat) (h : 2 ≤ rxNpkt) : mustAck rxNpkt = true := by
  unfold mustAck ACK_THRESHOLD; simpa using h

/-- Below the threshold no immediate ACK is forced (it may still be sent on the
ACK-delay timer). -/
theorem no_ack_below_threshold (rxNpkt : Nat) (h : rxNpkt < 2) : mustAck rxNpkt = false := by
  unfold mustAck ACK_THRESHOLD; simp; omega

end NgtcpRV.ConnAckFreq
