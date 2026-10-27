/-!
DATAGRAM frame size validation (conn.c, RFC 9221).

A DATAGRAM frame is only sent/accepted if the datagram plus its frame overhead
fits within the peer's advertised `max_datagram_frame_size`.  ngtcp2 computes
`write_datalen = datalen + NGTCP2_DATAGRAM_OVERHEAD` and the frame is admitted
only when it is within the limit.  We prove that an admitted datagram's wire size
never exceeds the advertised maximum (so a peer is never sent an over-size
datagram, and the size negotiation is respected).
-/
namespace NgtcpRV.ConnDatagram

/-- A datagram is admissible when its wire size (payload + overhead) fits the
advertised `max_datagram_frame_size`. -/
def admissible (datalen overhead maxSize : Nat) : Bool :=
  decide (datalen + overhead ≤ maxSize)

/-- **Within the advertised limit**: an admitted datagram's total wire size does
not exceed `max_datagram_frame_size`. -/
theorem admitted_fits (datalen overhead maxSize : Nat) (h : admissible datalen overhead maxSize = true) :
    datalen + overhead ≤ maxSize := by
  unfold admissible at h; simpa using h

/-- Therefore the payload itself is within `maxSize - overhead`. -/
theorem payload_bounded (datalen overhead maxSize : Nat) (h : admissible datalen overhead maxSize = true) :
    datalen ≤ maxSize - overhead := by
  have := admitted_fits datalen overhead maxSize h; omega

end NgtcpRV.ConnDatagram
