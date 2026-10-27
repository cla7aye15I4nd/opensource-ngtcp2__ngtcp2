import NgtcpRV.ConnAckEliciting
/-!
Packet-level ack-eliciting determination (conn.c, RFC 9000 §13.2.1).

A received packet is ack-eliciting — and so must be acknowledged — iff it contains
at least one ack-eliciting frame.  Building on `ConnAckEliciting` (the per-frame
predicate), we prove the per-packet predicate is exactly "some frame is
ack-eliciting", so a packet with only ACK/PADDING/CONNECTION_CLOSE frames does not
force an ACK, while any data frame does.
-/
namespace NgtcpRV.ConnPktAckEliciting
open NgtcpRV.ConnFrameAllow NgtcpRV.ConnAckEliciting

/-- A packet is ack-eliciting iff some frame in it is. -/
def packetAckEliciting (frames : List Frame) : Bool := frames.any isAckEliciting

theorem packet_elicits_iff (frames : List Frame) :
    packetAckEliciting frames = true ↔ ∃ f ∈ frames, isAckEliciting f = true := by
  unfold packetAckEliciting; rw [List.any_eq_true]

/-- A packet containing only non-ack-eliciting frames (ACK/PADDING/CONNECTION_CLOSE)
does not force an acknowledgement. -/
theorem no_elicit_of_all_non (frames : List Frame)
    (h : ∀ f ∈ frames, isAckEliciting f = false) :
    packetAckEliciting frames = false := by
  unfold packetAckEliciting
  rw [List.any_eq_false]
  intro f hf; simp [h f hf]

end NgtcpRV.ConnPktAckEliciting
