/-!
AEAD nonce uniqueness (crypto.c `ngtcp2_crypto_create_nonce`).

The packet-protection nonce is the IV with its low 8 bytes XORed with the packet
number (RFC 9001 §5.3): `n ^= htonl64(pkt_num)`.  AEAD security depends on the
nonce never repeating under one key — a nonce reuse is catastrophic for
confidentiality/integrity.  Since distinct packet numbers are never reused under
one key, the construction must map distinct packet numbers to distinct nonces.
We prove exactly that: XOR with a fixed IV is injective in the packet number, so
`create_nonce` never produces the same nonce for two different packet numbers.
(The low 8 bytes are modelled as `BitVec 64`; the rest of the IV is unchanged.)
-/
namespace NgtcpRV.CryptoNonce

/-- The nonce's low 8 bytes: `iv8 XOR pkt_num`. -/
def nonceTail (iv8 pktNum : BitVec 64) : BitVec 64 := iv8 ^^^ pktNum

/-- **Nonce uniqueness**: for a fixed IV, distinct packet numbers yield distinct
nonces — so under one key (where packet numbers never repeat) the AEAD nonce is
never reused. -/
theorem nonce_injective (iv8 pn1 pn2 : BitVec 64) (h : pn1 ≠ pn2) :
    nonceTail iv8 pn1 ≠ nonceTail iv8 pn2 := by
  unfold nonceTail
  intro heq
  apply h
  have hx : iv8 ^^^ (iv8 ^^^ pn1) = iv8 ^^^ (iv8 ^^^ pn2) := by rw [heq]
  rwa [← BitVec.xor_assoc, ← BitVec.xor_assoc, BitVec.xor_self,
       BitVec.zero_xor, BitVec.zero_xor] at hx

/-- Equivalent recovery form: the packet number is recoverable from nonce and IV
(`pkt_num = iv8 XOR nonce_tail`), confirming the map is a bijection in `pkt_num`. -/
theorem pktNum_recoverable (iv8 pktNum : BitVec 64) :
    iv8 ^^^ nonceTail iv8 pktNum = pktNum := by
  unfold nonceTail
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end NgtcpRV.CryptoNonce
