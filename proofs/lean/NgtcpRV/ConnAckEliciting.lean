import NgtcpRV.ConnFrameAllow
/-!
Ack-eliciting frame determination (conn.c, RFC 9000 §13.2.1).

A received packet elicits an acknowledgement iff it contains an "ack-eliciting"
frame.  PADDING, ACK (and ACK_ECN), and CONNECTION_CLOSE are NOT ack-eliciting;
every other frame type is.  Getting this right matters: treating an ACK-only
packet as ack-eliciting would cause ACK loops.  We reuse the frame enum from
`ConnFrameAllow` and prove the predicate matches the RFC exactly.
-/
namespace NgtcpRV.ConnAckEliciting
open NgtcpRV.ConnFrameAllow

/-- Whether a frame is ack-eliciting (requires the receiver to send an ACK). -/
def isAckEliciting : Frame → Bool
  | .padding | .ack | .connClose => false
  | _ => true

/-- **Non-ack-eliciting set**: a frame does NOT elicit an ACK iff it is PADDING,
ACK, or CONNECTION_CLOSE. -/
theorem not_ack_eliciting_iff (f : Frame) :
    isAckEliciting f = false ↔ (f = .padding ∨ f = .ack ∨ f = .connClose) := by
  cases f <;> simp [isAckEliciting]

/-- Data-bearing frames always elicit an ACK (so delivered data is acknowledged). -/
theorem data_frames_elicit :
    isAckEliciting .stream = true ∧ isAckEliciting .crypto = true ∧
    isAckEliciting .maxData = true ∧ isAckEliciting .datagram = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

end NgtcpRV.ConnAckEliciting
