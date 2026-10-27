/-!
Error-code varint bound (pkt.c, RFC 9000 §20).

QUIC transport and application error codes are carried as variable-length integers
in CONNECTION_CLOSE frames, so they fit in `[0, 2^62)`.  The standard transport
error codes (NO_ERROR=0 .. CRYPTO_ERROR range) are small.  We prove a validated
error code is encodable as a varint and the common codes are in the 1-byte range.
-/
namespace NgtcpRV.ConnErrorCode

/-- An error code is valid iff it fits in a QUIC varint. -/
def validErrorCode (code : Nat) : Bool := decide (code < 2 ^ 62)

theorem valid_fits_varint (code : Nat) (h : validErrorCode code = true) : code < 2 ^ 62 := by
  unfold validErrorCode at h; simpa using h

/-- The standard transport error codes (0x00..0x11) fit in a single varint byte
(`< 0x40`). -/
theorem standard_codes_one_byte (code : Nat) (h : code ≤ 0x11) : code < 0x40 := by omega

end NgtcpRV.ConnErrorCode
