/-!
STREAM frame type flag encoding (pkt.c, RFC 9000 §19.8).

A STREAM frame's type byte is `0x08 | (OFF<<2) | (LEN<<1) | FIN`, where OFF, LEN,
FIN are one-bit flags (offset-present, length-present, fin).  The decoder recovers
the three flags from the type.  We prove the encoding is an exact bijection, so
the frame parser reads the correct flags and the type stays in the valid STREAM
range `[0x08, 0x10)`.
-/
namespace NgtcpRV.ConnStreamFrameType

/-- The STREAM frame type byte for flags `off`, `len`, `fin` (each 0 or 1). -/
def streamType (off len fin : Nat) : Nat := 8 + 4 * off + 2 * len + fin

/-- **Flags recovered**: the decoder extracts `off`, `len`, `fin` exactly from the
type byte. -/
theorem streamType_recover (off len fin : Nat) (ho : off < 2) (hl : len < 2) (hf : fin < 2) :
    (streamType off len fin - 8) / 4 = off ∧
    (streamType off len fin - 8) / 2 % 2 = len ∧
    (streamType off len fin) % 2 = fin := by
  unfold streamType; omega

/-- The type byte is a valid STREAM frame type (`0x08..0x0f`). -/
theorem streamType_range (off len fin : Nat) (ho : off < 2) (hl : len < 2) (hf : fin < 2) :
    8 ≤ streamType off len fin ∧ streamType off len fin < 16 := by
  unfold streamType; omega

end NgtcpRV.ConnStreamFrameType
