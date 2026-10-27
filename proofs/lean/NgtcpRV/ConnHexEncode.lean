/-!
Hex-encoding correctness (str.c `ngtcp2_encode_hex`).

`ngtcp2_encode_hex` writes each byte as two lowercase hex digits
(`LOWER_XDIGITS[b>>4]`, `LOWER_XDIGITS[b&0xF]`), advancing `dest` by 2 per byte.
We prove the digit map is injective (so the output is decodable), each digit is a
valid ASCII hex character, and the byte is recoverable from its two nibbles.
-/
namespace NgtcpRV.ConnHexEncode

/-- `LOWER_XDIGITS[n]` for a nibble `n < 16`: `'0'..'9'` (48..57) or `'a'..'f'`
(97..102). -/
def hexChar (n : Nat) : Nat := if n < 10 then n + 48 else n + 87

/-- Each hex digit is a valid ASCII character (`'0'..'9'` or `'a'..'f'`). -/
theorem hexChar_range (n : Nat) (h : n < 16) :
    (48 ≤ hexChar n ∧ hexChar n ≤ 57) ∨ (97 ≤ hexChar n ∧ hexChar n ≤ 102) := by
  unfold hexChar; split <;> omega

/-- The digit map is injective on nibbles, so hex output is unambiguous/decodable. -/
theorem hexChar_injective (a b : Nat) (ha : a < 16) (hb : b < 16) (h : hexChar a = hexChar b) :
    a = b := by
  unfold hexChar at h; split at h <;> split at h <;> omega

/-- The two nibbles `(b>>4, b&0xF)` recover the byte: `16*(b>>4) + (b&0xF) = b`,
and for a byte (`b < 256`) both nibbles are `< 16`. -/
theorem byte_from_nibbles (b : Nat) (h : b < 256) :
    16 * (b / 16) + b % 16 = b ∧ b / 16 < 16 ∧ b % 16 < 16 := by
  omega

end NgtcpRV.ConnHexEncode
