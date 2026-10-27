/-!
Frame-type admissibility in Initial/Handshake packets (conn.c
`conn_recv_handshake_pkt`, RFC 9000 §12.4 / §17.2).

Initial and Handshake packets may carry ONLY PADDING, PING, ACK, CRYPTO, and
CONNECTION_CLOSE frames; every other frame type is a protocol violation
(`default: return NGTCP2_ERR_PROTO`).  This keeps application data and
connection-management frames out of the unauthenticated/early encryption levels.
We model the frame-type switch and prove it admits exactly the allowed set and
rejects all data-bearing / management frames.
-/
namespace NgtcpRV.ConnFrameAllow

inductive Frame where
  | padding | ping | ack | crypto | connClose          -- allowed in handshake
  | stream | maxData | maxStreamData | newConnectionId  -- NOT allowed
  | resetStream | stopSending | newToken | datagram
deriving DecidableEq

/-- The handshake-packet frame switch: `true` for the five allowed types, else
`false` (the `default: NGTCP2_ERR_PROTO` arm). -/
def handshakeAllowed : Frame → Bool
  | .padding | .ping | .ack | .crypto | .connClose => true
  | _ => false

/-- **Soundness**: a frame is admitted in a handshake packet iff it is one of the
five RFC-permitted types. -/
theorem handshakeAllowed_iff (f : Frame) :
    handshakeAllowed f = true ↔
      (f = .padding ∨ f = .ping ∨ f = .ack ∨ f = .crypto ∨ f = .connClose) := by
  cases f <;> simp [handshakeAllowed]

/-- Data-bearing and connection-management frames are rejected at the handshake
level (they belong only to 1-RTT). -/
theorem handshake_rejects_data :
    handshakeAllowed .stream = false ∧
    handshakeAllowed .maxData = false ∧
    handshakeAllowed .maxStreamData = false ∧
    handshakeAllowed .newConnectionId = false ∧
    handshakeAllowed .resetStream = false ∧
    handshakeAllowed .stopSending = false ∧
    handshakeAllowed .newToken = false ∧
    handshakeAllowed .datagram = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end NgtcpRV.ConnFrameAllow
