/-!
Version-Negotiation list parsing (pkt.c `ngtcp2_pkt_decode_version_negotiation`,
RFC 9000 §17.2.1).

A Version Negotiation packet carries a list of supported versions, each a 4-byte
value.  The payload length must be a positive multiple of 4, and the version count
is `payloadlen / 4`.  We prove that a validated payload length yields a whole
number of 4-byte versions with no leftover bytes, so the parser reads exactly
`count` versions without overrunning.
-/
namespace NgtcpRV.ConnVersionNegList

/-- The VN payload must be a positive multiple of 4 bytes. -/
def validLen (payloadlen : Nat) : Bool := decide (payloadlen % 4 = 0 ∧ 0 < payloadlen)

/-- A validated length is exactly `count * 4` bytes for `count = payloadlen / 4`
versions (no leftover bytes), and `count >= 1`. -/
theorem vn_version_count (payloadlen : Nat) (h : validLen payloadlen = true) :
    payloadlen = (payloadlen / 4) * 4 ∧ 1 ≤ payloadlen / 4 := by
  unfold validLen at h
  simp only [decide_eq_true_eq] at h
  omega

/-- Every 4-byte version slot `[4*i, 4*i+4)` for `i < count` stays within the
payload. -/
theorem version_slot_in_bounds (payloadlen i : Nat) (h : validLen payloadlen = true)
    (hi : i < payloadlen / 4) : 4 * i + 4 ≤ payloadlen := by
  have := vn_version_count payloadlen h; omega

end NgtcpRV.ConnVersionNegList
