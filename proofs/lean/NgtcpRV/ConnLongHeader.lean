/-!
Long-header first-byte decoding (pkt.c, RFC 9000 §17.2).

A long-header packet's first byte is `0x80 | 0x40 | (type << 4) | type_specific`,
where bit 7 = 1 (long form), bit 6 = 1 (fixed bit), bits 5-4 = packet type
(Initial=0, 0-RTT=1, Handshake=2, Retry=3), and bits 3-0 are type-specific (the
packet-number length minus one for Initial/0-RTT/Handshake).  We prove the header
form and the packet type are recovered exactly from the first byte.
-/
namespace NgtcpRV.ConnLongHeader

/-- Long-header first byte for packet type `t` and a 4-bit type-specific field. -/
def firstByte (t specific : Nat) : Nat := 0xC0 + t * 16 + specific

/-- **Long-form flag and type recovered**: bit 7 marks the long header, and bits
5-4 recover the packet type exactly. -/
theorem decode_long_header (t specific : Nat) (ht : t < 4) (hs : specific < 16) :
    firstByte t specific / 128 = 1 ∧              -- bit 7 (long form)
    firstByte t specific / 64 % 2 = 1 ∧           -- bit 6 (fixed bit)
    firstByte t specific / 16 % 4 = t ∧           -- bits 5-4 (packet type)
    firstByte t specific % 16 = specific := by     -- bits 3-0 (type-specific)
  unfold firstByte; omega

/-- The first byte is a valid long-header byte (`0xC0..0xFF`). -/
theorem firstByte_range (t specific : Nat) (ht : t < 4) (hs : specific < 16) :
    0xC0 ≤ firstByte t specific ∧ firstByte t specific < 256 := by
  unfold firstByte; omega

end NgtcpRV.ConnLongHeader
