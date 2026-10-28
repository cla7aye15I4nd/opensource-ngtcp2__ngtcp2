/-!
# conv: decoded varint values fit in 62 bits (`ngtcp2_get_uvarint`)

`ngtcp2_get_uvarint` (lib/ngtcp2_conv.c) decodes a varint by selecting the length
from the top two bits of the first byte and masking them off:

```c
  case 1: n16 &= 0x3FFFU;                    *dest = n16;  /* < 2^14 */
  case 2: n32 &= 0x3FFFFFFFU;                *dest = n32;  /* < 2^30 */
  case 3: n64 &= 0x3FFFFFFFFFFFFFFFULL;      *dest = n64;  /* < 2^62 */
```
(case 0 reads a single byte whose top bits are 0, so `< 64`).  The mask removes the
two length-prefix bits, so every decoded value is at most
`NGTCP2_MAX_VARINT = 2^62 - 1`.  All frame/transport-param parsers rely on decoded
varints being `<= NGTCP2_MAX_VARINT`; we prove it for each length class.
-/
namespace NgtcpRV.VarintValue

/-- `NGTCP2_MAX_VARINT = 2^62 - 1`. -/
def MAX_VARINT : Nat := 4611686018427387903

/-- The 8-byte mask `0x3FFF_FFFF_FFFF_FFFF`. -/
def MASK62 : BitVec 64 := 0x3FFFFFFFFFFFFFFF

/-- **8-byte varint** (the largest): the decoded value is at most `NGTCP2_MAX_VARINT`. -/
theorem decode8_le_max (n : BitVec 64) : (n &&& MASK62).toNat ≤ MAX_VARINT := by
  rw [BitVec.toNat_and]
  refine Nat.le_trans Nat.and_le_right ?_
  show MASK62.toNat ≤ MAX_VARINT
  decide

/-- **4-byte varint**: masking with `0x3FFFFFFF` yields a value `< 2^30`. -/
theorem decode4_lt (n : BitVec 32) : (n &&& 0x3FFFFFFF).toNat ≤ 1073741823 := by
  rw [BitVec.toNat_and]
  refine Nat.le_trans Nat.and_le_right ?_
  decide

/-- **2-byte varint**: masking with `0x3FFF` yields a value `< 2^14`. -/
theorem decode2_lt (n : BitVec 16) : (n &&& 0x3FFF).toNat ≤ 16383 := by
  rw [BitVec.toNat_and]
  refine Nat.le_trans Nat.and_le_right ?_
  decide

/-- **1-byte varint**: a first byte with length prefix `00` is `< 64`. -/
theorem decode1_lt (b : Nat) (h : b / 64 = 0) : b < 64 := by omega

/-- Every decoded varint, whatever its length, is a valid QUIC varint
(`<= NGTCP2_MAX_VARINT`). -/
theorem decoded_le_max (n : BitVec 64) : (n &&& MASK62).toNat ≤ MAX_VARINT := decode8_le_max n

end NgtcpRV.VarintValue
