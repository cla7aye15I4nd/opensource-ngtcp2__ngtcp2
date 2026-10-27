/-!
Header-protection sample/mask lengths (crypto, RFC 9001 §5.4).

Header protection samples `NGTCP2_HP_SAMPLELEN = 16` bytes of ciphertext and
derives a mask, of which the low bytes protect the first byte (1) and the
packet-number bytes (up to 4), i.e. at most `NGTCP2_HP_MASKLEN = 5` mask bytes are
applied.  We prove the applied mask fits within the sample-derived mask and that
masking covers at most the 1 header byte + 4 pkt-num bytes.
-/
namespace NgtcpRV.ConnHpLengths

def HP_SAMPLELEN : Nat := 16
def HP_MASKLEN : Nat := 5

/-- The applied mask (5 bytes) fits within the 16-byte sample. -/
theorem mask_within_sample : HP_MASKLEN ≤ HP_SAMPLELEN := by decide

/-- The mask covers exactly the first byte plus up to 4 packet-number bytes. -/
theorem mask_covers_header (pnLen : Nat) (h : pnLen ≤ 4) : 1 + pnLen ≤ HP_MASKLEN := by
  unfold HP_MASKLEN; omega

end NgtcpRV.ConnHpLengths
