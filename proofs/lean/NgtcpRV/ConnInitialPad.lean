/-!
Initial-packet padding requirement (conn.c, RFC 9000 §14.1).

A client's Initial packet (and any datagram carrying an ack-eliciting Initial)
MUST be padded to at least `NGTCP2_MAX_UDP_PAYLOAD_SIZE = 1200` bytes.  This forces
the handshake to pay its own way (anti-amplification).  ngtcp2 sets
`require_padding` for such datagrams and pads to 1200.  We prove that when padding
is required, the resulting datagram is at least 1200 bytes.
-/
namespace NgtcpRV.ConnInitialPad

def MIN_INITIAL : Nat := 1200

/-- The datagram length after applying the Initial-padding rule: padded up to the
minimum when required, else left as-is. -/
def paddedLen (len : Nat) (requirePadding : Bool) : Nat :=
  if requirePadding then max len MIN_INITIAL else len

/-- **Ack-eliciting Initial is full-size**: when padding is required, the datagram
reaches at least the 1200-byte minimum. -/
theorem required_padding_reaches_min (len : Nat) (h : requirePadding = true) :
    MIN_INITIAL ≤ paddedLen len requirePadding := by
  unfold paddedLen; rw [if_pos h]; omega

/-- Padding never shrinks the datagram. -/
theorem padding_no_shrink (len : Nat) (requirePadding : Bool) :
    len ≤ paddedLen len requirePadding := by
  unfold paddedLen; split <;> omega

end NgtcpRV.ConnInitialPad
