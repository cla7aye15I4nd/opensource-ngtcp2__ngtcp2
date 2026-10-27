/-!
Version field semantics (pkt.c, RFC 9000 §17.2.1 / RFC 8999).

In a long-header packet the 32-bit Version field selects the QUIC version; the
reserved value 0 marks a Version Negotiation packet (it is never a real version).
QUIC v1 is `0x00000001` and QUIC v2 is `0x6b3343cf`.  We prove version 0 (VN) is
distinct from the real versions, so a VN packet is never mistaken for a v1/v2
packet and vice versa.
-/
namespace NgtcpRV.ConnVersion

def QUIC_V1 : Nat := 0x00000001
def QUIC_V2 : Nat := 0x6b3343cf

/-- A Version Negotiation packet carries version 0. -/
def isVersionNegotiation (version : Nat) : Bool := decide (version = 0)

/-- VN (version 0) is distinct from QUIC v1 and v2. -/
theorem vn_not_v1 : isVersionNegotiation QUIC_V1 = false := by decide
theorem vn_not_v2 : isVersionNegotiation QUIC_V2 = false := by decide

/-- v1 and v2 are distinct versions. -/
theorem v1_ne_v2 : QUIC_V1 ≠ QUIC_V2 := by decide

/-- A real (nonzero) version is never classified as Version Negotiation. -/
theorem real_version_not_vn (v : Nat) (h : v ≠ 0) : isVersionNegotiation v = false := by
  unfold isVersionNegotiation; simp [h]

end NgtcpRV.ConnVersion
