import NgtcpRV.ConnFrameAllow
/-!
Retransmittable-frame determination (conn.c / rtb.c, RFC 9000 §13.3).

On packet loss, most frames are retransmitted (in a new packet), but some are not:
ACK and PADDING carry no retransmittable content, CONNECTION_CLOSE is handled
separately, and DATAGRAM frames are unreliable (ngtcp2 does not retransmit them).
We reuse the frame enum and prove the retransmittable predicate matches this.
-/
namespace NgtcpRV.ConnRetransmittable
open NgtcpRV.ConnFrameAllow

/-- Whether a frame is retransmitted on loss. -/
def isRetransmittable : Frame → Bool
  | .padding | .ack | .connClose | .datagram => false
  | _ => true

/-- Non-retransmittable frames are exactly PADDING/ACK/CONNECTION_CLOSE/DATAGRAM. -/
theorem not_retransmittable_iff (f : Frame) :
    isRetransmittable f = false ↔
      (f = .padding ∨ f = .ack ∨ f = .connClose ∨ f = .datagram) := by
  cases f <;> simp [isRetransmittable]

/-- Reliable control/data frames (STREAM, CRYPTO, MAX_DATA, RESET_STREAM) are
retransmitted, so their delivery is guaranteed despite loss. -/
theorem reliable_frames_retransmitted :
    isRetransmittable .stream = true ∧ isRetransmittable .crypto = true ∧
    isRetransmittable .maxData = true ∧ isRetransmittable .resetStream = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

end NgtcpRV.ConnRetransmittable
