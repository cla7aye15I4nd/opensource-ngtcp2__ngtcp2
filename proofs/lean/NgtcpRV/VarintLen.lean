/-!
# conv: varint length functions (`ngtcp2_get_uvarintlen` / `ngtcp2_put_uvarintlen`)

Every QUIC frame/transport-parameter parser reads varints, and their on-wire length
comes from `ngtcp2_get_uvarintlen` (lib/ngtcp2_conv.c:194):

```c
  size_t ngtcp2_get_uvarintlen(const uint8_t *p) { return (size_t)(1U << (*p >> 6)); }
```
The top two bits of the first byte select the length, which is therefore always one
of {1,2,4,8} — and in particular **≤ 8**.  That bound is exactly what makes the
parsers' incremental length checks sound (e.g. AckDecodeSafe / the frame decoders
all advance by a varint length).  `ngtcp2_put_uvarintlen` (line 198) returns the
minimal number of bytes for a value and also always yields {1,2,4,8}.

We prove both length functions land in {1,2,4,8}, that the read length is ≤ 8, and
that `put_uvarintlen` classifies values into the correct RFC 9000 buckets.
-/
namespace NgtcpRV.VarintLen

/-- `ngtcp2_get_uvarintlen`: `1 << (byte >> 6)` = `2 ^ (byte / 64)`. -/
def getLen (byte : Nat) : Nat := 2 ^ (byte / 64)

/-- For a real byte (`< 256`), the varint read length is at most 8. -/
theorem getLen_le_8 (b : Nat) (h : b < 256) : getLen b ≤ 8 := by
  unfold getLen
  have hb : b / 64 ≤ 3 := by omega
  calc 2 ^ (b / 64) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) hb
    _ = 8 := by decide

/-- The varint read length is always at least 1 (at least one byte is consumed). -/
theorem getLen_pos (b : Nat) : 1 ≤ getLen b := Nat.one_le_two_pow

/-- The read length is exactly one of {1,2,4,8}. -/
theorem getLen_mem (b : Nat) (h : b < 256) :
    getLen b = 1 ∨ getLen b = 2 ∨ getLen b = 4 ∨ getLen b = 8 := by
  unfold getLen
  have hk : b / 64 = 0 ∨ b / 64 = 1 ∨ b / 64 = 2 ∨ b / 64 = 3 := by omega
  rcases hk with h | h | h | h <;> rw [h] <;> decide

/-- `ngtcp2_put_uvarintlen`: the minimal bytes to encode `n` (RFC 9000 buckets). -/
def putLen (n : Nat) : Nat :=
  if n < 64 then 1 else if n < 16384 then 2 else if n < 1073741824 then 4 else 8

/-- `put_uvarintlen` also lands in {1,2,4,8}. -/
theorem putLen_mem (n : Nat) :
    putLen n = 1 ∨ putLen n = 2 ∨ putLen n = 4 ∨ putLen n = 8 := by
  unfold putLen
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · split
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))

/-- `put_uvarintlen` never exceeds 8. -/
theorem putLen_le_8 (n : Nat) : putLen n ≤ 8 := by
  rcases putLen_mem n with h | h | h | h <;> omega

/-- Bucket correctness (smallest size): a value below 64 encodes in a single byte. -/
theorem putLen_small (n : Nat) (h : n < 64) : putLen n = 1 := by
  unfold putLen; rw [if_pos h]

/-- The largest varint holds values below `2^62`, and such values never need more
than 8 bytes (consistent with `get`'s maximum). -/
theorem putLen_fits_62 (n : Nat) (h : n < 4611686018427387904) : putLen n ≤ 8 := putLen_le_8 n

end NgtcpRV.VarintLen
