/-!
Short-header (1-RTT) first-byte decoding (pkt.c, RFC 9000 §17.3).

A 1-RTT packet's first byte is `0x40 | (spin<<5) | (keyphase<<2) | (pnlen-1)`:
bit 7 = 0 (short form), bit 6 = 1 (fixed), bit 5 = spin, bit 2 = key phase, bits
1-0 = packet-number length minus one.  We prove the short-form flag, key phase and
packet-number length are recovered exactly — in particular the key-phase bit,
which selects the decryption keys, is read correctly.
-/
namespace NgtcpRV.ConnShortHeader

/-- Short-header first byte for a spin bit, key phase, and pnlen in `{1,2,3,4}`. -/
def firstByte (spin keyphase pnlen : Nat) : Nat := 0x40 + spin * 32 + keyphase * 4 + (pnlen - 1)

/-- **Short-form, key phase and pnlen recovered**: the decoder reads the correct
key-phase bit (which chooses the keys) and packet-number length. -/
theorem decode_short_header (spin keyphase pnlen : Nat)
    (hsp : spin < 2) (hk : keyphase < 2) (hp : 1 ≤ pnlen) (hp2 : pnlen ≤ 4) :
    firstByte spin keyphase pnlen / 128 = 0 ∧        -- bit 7 = 0 (short form)
    firstByte spin keyphase pnlen / 4 % 2 = keyphase ∧  -- bit 2 (key phase)
    firstByte spin keyphase pnlen % 4 + 1 = pnlen := by  -- bits 1-0 + 1 (pnlen)
  unfold firstByte; omega

end NgtcpRV.ConnShortHeader
