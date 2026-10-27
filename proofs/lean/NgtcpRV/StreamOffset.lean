/-!
Stream-offset arithmetic safety (strm.c / conn.c STREAM/CRYPTO frame handling).

Receiving a STREAM frame at `offset` with `datalen` bytes computes the end offset
`offset + datalen` to check it against the flow-control limit and to update the
reorder buffer.  Both `offset` and `datalen` are QUIC varints (`< 2^62`), so the
sum is `< 2^63` and never overflows `uint64` — the end offset is exact.  We prove
there is no wraparound, so the limit check and reassembly use the true end offset.
Modelled over `BitVec 64`.
-/
namespace NgtcpRV.StreamOffset

/-- `2^62`, the varint ceiling. -/
def B62 : BitVec 64 := 0x4000000000000000#64

/-- **No overflow in the end-offset computation**: for varint `offset, datalen
< 2^62`, the sum `offset + datalen` does not wrap, so its value is exactly
`offset + datalen` and stays `< 2^63`. -/
theorem end_offset_exact (offset datalen : BitVec 64)
    (ho : offset < B62) (hd : datalen < B62) :
    (offset + datalen).toNat = offset.toNat + datalen.toNat ∧
    (offset + datalen).toNat < 2 ^ 63 := by
  unfold B62 at ho hd
  constructor
  · bv_omega
  · bv_omega

/-- Monotonicity of the end offset: more data never lowers the end offset
(`offset <= offset + datalen`), so a stream's high-water mark only advances. -/
theorem end_offset_ge (offset datalen : BitVec 64)
    (ho : offset < B62) (hd : datalen < B62) :
    offset ≤ offset + datalen := by
  unfold B62 at ho hd; bv_omega

end NgtcpRV.StreamOffset
