/-!
max_udp_payload_size validation (transport_params.c, RFC 9000 §18.2).

The transport parameter `max_udp_payload_size` MUST be at least 1200 bytes (the
QUIC minimum maximum datagram size); a smaller value is a
TRANSPORT_PARAMETER_ERROR.  This guarantees the path can carry a full-size Initial
packet.  We prove the validation establishes the `>= 1200` lower bound, so the
shaped UDP payload (`ConnPkt.shape`) always has at least the minimum to work with.
-/
namespace NgtcpRV.ConnMaxUdpPayload

def MIN_UDP_PAYLOAD : Nat := 1200

/-- The validation: `max_udp_payload_size` must be at least 1200. -/
def validUdpSize (n : Nat) : Bool := decide (MIN_UDP_PAYLOAD ≤ n)

/-- **At least the minimum datagram size**: a validated `max_udp_payload_size` is
`>= 1200`, so a full Initial packet always fits. -/
theorem udp_size_ge_min (n : Nat) (h : validUdpSize n = true) : 1200 ≤ n := by
  unfold validUdpSize MIN_UDP_PAYLOAD at h; simpa using h

end NgtcpRV.ConnMaxUdpPayload
