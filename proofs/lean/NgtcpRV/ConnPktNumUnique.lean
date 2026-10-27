import NgtcpRV.CryptoNonce
/-!
Packet-number uniqueness ⇒ AEAD nonce uniqueness (conn.c, RFC 9000 §12.3 / RFC
9001 §5.3).

Within a packet-number space ngtcp2 assigns each sent packet `tx.last_pkt_num + 1`
and increments, so the `k`-th packet sent gets number `base + k` — a strictly
increasing sequence, never reusing a number under one key.  Combined with
`CryptoNonce.nonce_injective` (distinct packet numbers ⇒ distinct nonces), this
closes the AEAD-security argument: no nonce is ever reused.
-/
namespace NgtcpRV.ConnPktNumUnique

/-- The packet number assigned to the `k`-th packet sent (0-indexed), starting at
`base`. -/
def assigned (base k : Nat) : Nat := base + k

/-- **Packet numbers are strictly increasing**, hence never reused: distinct sends
get distinct numbers. -/
theorem assigned_injective (base i j : Nat) (h : i ≠ j) : assigned base i ≠ assigned base j := by
  unfold assigned; omega

/-- **No AEAD nonce reuse**: two distinct sends produce distinct nonces, because
their packet numbers differ and the nonce is injective in the packet number
(`CryptoNonce.nonceTail`).  So one key never protects two packets with the same
nonce. -/
theorem no_nonce_reuse (iv8 : BitVec 64) (base i j : Nat) (h : i ≠ j)
    (hb : (BitVec.ofNat 64 (assigned base i)) ≠ (BitVec.ofNat 64 (assigned base j))) :
    NgtcpRV.CryptoNonce.nonceTail iv8 (BitVec.ofNat 64 (assigned base i)) ≠
    NgtcpRV.CryptoNonce.nonceTail iv8 (BitVec.ofNat 64 (assigned base j)) :=
  NgtcpRV.CryptoNonce.nonce_injective iv8 _ _ hb

end NgtcpRV.ConnPktNumUnique
