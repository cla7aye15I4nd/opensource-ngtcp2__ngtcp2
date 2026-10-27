import NgtcpRV.ConnVarintLen
/-!
QUIC varint encode/decode roundtrip (conv.c `ngtcp2_put_uvarint` / `ngtcp2_get_uvarint`).

A varint stores the value in the low `8*L - 2` bits of an `L`-byte field, with the
top 2 bits a length prefix `plog L ∈ {0,1,2,3}` for `L ∈ {1,2,4,8}` (RFC 9000 §16).
The encoded field is `plog L * 2^(8L-2) + n`.  Decoding recovers the length (from
the top 2 bits) and the value (the low `8L-2` bits).  Building on `ConnVarintLen`,
we prove the roundtrip: decode recovers both the length prefix and the value `n`
exactly, for every `n < 2^62`.
-/
namespace NgtcpRV.VarintRoundtrip
open NgtcpRV.ConnVarintLen

/-- The 2-bit length prefix for an `L`-byte varint. -/
def plog (L : Nat) : Nat := if L = 1 then 0 else if L = 2 then 1 else if L = 4 then 2 else 3

/-- The encoded varint field: length prefix in the top 2 bits, value below. -/
def encode (n : Nat) : Nat := plog (varintLen n) * 2 ^ (8 * varintLen n - 2) + n

/-- **Varint roundtrip**: from the encoded field, the low `8L-2` bits recover the
value `n`, and the top bits recover the length prefix `plog L` — decode is the
exact inverse of encode, for every valid varint. -/
theorem roundtrip (n : Nat) (h : n < 2 ^ 62) :
    encode n % 2 ^ (8 * varintLen n - 2) = n ∧
    encode n / 2 ^ (8 * varintLen n - 2) = plog (varintLen n) := by
  unfold encode
  have hw : n < 2 ^ (8 * varintLen n - 2) := varintLen_width n h
  have hwpos : 0 < 2 ^ (8 * varintLen n - 2) := Nat.pow_pos (by omega)
  constructor
  · rw [Nat.mul_add_mod']; exact Nat.mod_eq_of_lt hw
  · rw [Nat.mul_comm, Nat.mul_add_div hwpos, Nat.div_eq_of_lt hw, Nat.add_zero]

end NgtcpRV.VarintRoundtrip
