/-!
Stream-ID structure (conn.c / ngtcp2_strm, RFC 9000 §2.1).

A QUIC stream ID's low 2 bits encode the type: bit 0 = initiator (0 client,
1 server), bit 1 = directionality (0 bidi, 1 uni).  The `n`-th stream of a given
type has ID `4*n + type`, and ngtcp2 recovers the per-type index with `id >> 2`
(= `id / 4`, used by `ngtcp2_idtr`) and the type with `id & 3`.  We prove this is
an exact bijection, so stream accounting and the per-type limits are consistent.
-/
namespace NgtcpRV.ConnStreamId

/-- The ID of the `n`-th stream of type `t` (`t ∈ {0,1,2,3}`). -/
def streamId (n t : Nat) : Nat := 4 * n + t

/-- **Index/type recovery**: `id >> 2` recovers the per-type index `n` and
`id & 3` recovers the type `t` — the encoding is injective. -/
theorem streamId_recover (n t : Nat) (ht : t < 4) :
    streamId n t / 4 = n ∧ streamId n t % 4 = t := by
  unfold streamId; omega

/-- Conversely every stream ID decomposes uniquely: `id = 4 * (id/4) + (id%4)`
with the type `id % 4 < 4`. -/
theorem streamId_decompose (sid : Nat) :
    sid = streamId (sid / 4) (sid % 4) ∧ sid % 4 < 4 := by
  unfold streamId; omega

/-- The initiator bit (`id & 1`) and directionality bit (`(id >> 1) & 1`) are
exactly the two bits of the type, so the four stream types partition all IDs. -/
theorem streamId_type_bits (sid : Nat) :
    sid % 2 = (sid % 4) % 2 ∧ sid / 2 % 2 = sid % 4 / 2 := by
  omega

end NgtcpRV.ConnStreamId
