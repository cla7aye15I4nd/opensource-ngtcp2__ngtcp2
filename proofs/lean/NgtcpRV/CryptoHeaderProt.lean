/-!
Header-protection reversibility (crypto / pkt.c).

QUIC header protection XORs the masked header bits (the first byte's low bits and
the packet-number bytes) with a mask derived from a sample of the ciphertext
(RFC 9001 §5.4).  The receiver removes protection by XORing with the SAME mask.
Correctness requires this be exactly reversible: unprotect ∘ protect = id, so a
packet the sender protected is recovered bit-for-bit.  We prove the XOR mask is
involutive, per byte and over the whole masked region.
-/
namespace NgtcpRV.CryptoHeaderProt

/-- Apply the header-protection mask to one byte. -/
def mask1 (b m : BitVec 8) : BitVec 8 := b ^^^ m

/-- One byte: applying the mask twice restores the original. -/
theorem mask1_involutive (b m : BitVec 8) : mask1 (mask1 b m) m = b := by
  unfold mask1
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Apply the mask across the masked header region (header byte + pkt-num bytes). -/
def maskBytes (data mask : List (BitVec 8)) : List (BitVec 8) :=
  List.zipWith (· ^^^ ·) data mask

/-- **Header protection is reversible**: XORing the masked region with the mask
twice recovers the original bytes exactly — so removing header protection with the
same mask restores the sender's header bit-for-bit. -/
theorem maskBytes_involutive (data mask : List (BitVec 8))
    (h : data.length ≤ mask.length) :
    maskBytes (maskBytes data mask) mask = data := by
  unfold maskBytes
  induction data generalizing mask with
  | nil => simp
  | cons d ds ih =>
    cases mask with
    | nil => simp at h
    | cons m ms =>
      simp only [List.zipWith_cons_cons, List.length_cons] at *
      have h1 : (d ^^^ m) ^^^ m = d := by
        rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      have h2 := ih ms (by omega)
      rw [h1, h2]

end NgtcpRV.CryptoHeaderProt
