/-!
QUIC varint length selection (conv.c `ngtcp2_put_uvarintlen`).

A QUIC varint encodes a value `< 2^62` in 1/2/4/8 bytes, top 2 bits a length
prefix, payload holding 6/14/30/62 bits (RFC 9000 §16).  We prove the
magnitude-chosen length always has capacity for the value (so `put_uvarint`
never truncates) and is a legal length.
-/
namespace NgtcpRV.ConnVarintLen

def varintLen (n : Nat) : Nat :=
  if n < 2 ^ 6 then 1 else if n < 2 ^ 14 then 2 else if n < 2 ^ 30 then 4 else 8

theorem varintLen_mem (n : Nat) :
    varintLen n = 1 ∨ varintLen n = 2 ∨ varintLen n = 4 ∨ varintLen n = 8 := by
  unfold varintLen; (repeat' split) <;> omega

/-- **Capacity**: the chosen length holds the value without truncation. -/
theorem varintLen_holds (n : Nat) (h : n < 2 ^ 62) :
    (varintLen n = 1 → n < 2 ^ 6) ∧
    (varintLen n = 2 → n < 2 ^ 14) ∧
    (varintLen n = 4 → n < 2 ^ 30) ∧
    (varintLen n = 8 → n < 2 ^ 62) := by
  unfold varintLen
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (repeat' split) <;> omega

/-- The encoded payload width (`8*len - 2` bits) always covers the value. -/
theorem varintLen_width (n : Nat) (h : n < 2 ^ 62) : n < 2 ^ (8 * varintLen n - 2) := by
  unfold varintLen; (repeat' split) <;> omega

end NgtcpRV.ConnVarintLen
