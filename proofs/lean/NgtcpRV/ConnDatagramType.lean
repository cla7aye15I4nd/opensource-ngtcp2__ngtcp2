/-!
DATAGRAM frame-type encoding (pkt.c, RFC 9221 §4).

A DATAGRAM frame type is `0x30 | LEN`, where the low bit indicates whether an
explicit Length field is present (`0x30` = no length / rest-of-packet, `0x31` =
length-prefixed).  We prove the LEN flag is recovered exactly and the type stays in
the valid DATAGRAM range.
-/
namespace NgtcpRV.ConnDatagramType

/-- DATAGRAM frame type for the LEN flag (0 or 1). -/
def datagramType (hasLen : Nat) : Nat := 0x30 + hasLen

/-- The LEN flag is recovered exactly from the type byte. -/
theorem datagram_len_recover (hasLen : Nat) (h : hasLen < 2) :
    datagramType hasLen - 0x30 = hasLen ∧ datagramType hasLen % 2 = hasLen := by
  unfold datagramType; omega

/-- The type is a valid DATAGRAM frame type (0x30 or 0x31). -/
theorem datagram_type_range (hasLen : Nat) (h : hasLen < 2) :
    0x30 ≤ datagramType hasLen ∧ datagramType hasLen ≤ 0x31 := by
  unfold datagramType; omega

end NgtcpRV.ConnDatagramType
