/-!
Big-endian uint64 encode/decode roundtrip (conv.c `ngtcp2_put_uint64be` /
`ngtcp2_get_uint64be`).

`put_uint64be` writes a `uint64_t` as 8 big-endian bytes; `get_uint64be` reads
them back.  Reading back what was written must recover the original value
(every QUIC integer field on the wire depends on this).  We prove the roundtrip
`get64be (put64be n) = n` for every `n < 2^64`, at the value level.  (The
machine-code/CBMC proofs cover the byte-level memory safety; this is the
functional roundtrip.)
-/
namespace NgtcpRV.ConvRoundtrip

/-- `ngtcp2_put_uint64be n`: the 8 big-endian bytes (most significant first). -/
def put64be (n : Nat) : List Nat :=
  [n / 256^7 % 256, n / 256^6 % 256, n / 256^5 % 256, n / 256^4 % 256,
   n / 256^3 % 256, n / 256^2 % 256, n / 256^1 % 256, n / 256^0 % 256]

/-- `ngtcp2_get_uint64be`: reassemble a big-endian byte list back into a value. -/
def get64be : List Nat → Nat
  | [b0, b1, b2, b3, b4, b5, b6, b7] =>
    b0 * 256^7 + b1 * 256^6 + b2 * 256^5 + b3 * 256^4 +
    b4 * 256^3 + b5 * 256^2 + b6 * 256^1 + b7 * 256^0
  | _ => 0

/-- **Encode/decode roundtrip**: reading back the big-endian encoding of any
`uint64_t` recovers the original value exactly. -/
theorem get_put (n : Nat) (h : n < 2 ^ 64) : get64be (put64be n) = n := by
  simp only [put64be, get64be]
  omega

/-- The encoding is exactly 8 bytes. -/
theorem put64be_length (n : Nat) : (put64be n).length = 8 := rfl

end NgtcpRV.ConvRoundtrip
