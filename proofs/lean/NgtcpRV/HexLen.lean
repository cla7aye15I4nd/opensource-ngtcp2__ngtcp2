/-!
# conv: hex-encoding length is bounded `ngtcp2_encode_uint_hexlen` (lib/ngtcp2_str.c)

`ngtcp2_encode_uint_hexlen(n)` returns the number of hex digits needed to print a
`uint64_t` (1 for `n == 0`, otherwise the minimal nibble count); callers allocate that
many bytes and `ngtcp2_encode_uint_hex` writes exactly that many.  For buffer safety the
returned length must be bounded: a 64-bit value needs at most 16 hex digits.

We capture the length's defining contract (`16^(L-1) <= n` for `n > 0`, `L >= 1`) and
prove it yields `1 <= L <= 16` for any `n < 16^16 = 2^64` — so a fixed 16-byte hex buffer
never overflows.
-/
namespace NgtcpRV.HexLen

/-- The contract of `ngtcp2_encode_uint_hexlen`: at least one digit, and (for `n > 0`)
the top digit is significant, i.e. `16^(L-1) <= n`. -/
def HexLenValid (n L : Nat) : Prop := 0 < L ∧ (0 < n → 16 ^ (L - 1) ≤ n)

/-- The length is always at least 1. -/
theorem hexlen_ge_1 (n L : Nat) (h : HexLenValid n L) : 1 ≤ L := h.1

/-- **Buffer bound**: a value below `16^16 = 2^64` needs at most 16 hex digits. -/
theorem hexlen_le_16 (n L : Nat) (hn : n < 16 ^ 16) (h : HexLenValid n L) (hpos : 0 < n) :
    L ≤ 16 := by
  rcases Nat.lt_or_ge L 17 with h17 | h17
  · omega
  · exfalso
    have hle : (16 : Nat) ≤ L - 1 := by omega
    have : (16 : Nat) ^ 16 ≤ 16 ^ (L - 1) := Nat.pow_le_pow_right (by decide) hle
    have hn2 := h.2 hpos
    omega

end NgtcpRV.HexLen
