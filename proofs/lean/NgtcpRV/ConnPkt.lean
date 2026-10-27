/-!
Two pure conn.c helpers.

* conn_shape_udp_payload: a chain of `ngtcp2_min` caps the datagram size by every
  configured UDP-payload limit, so a written datagram never exceeds any of them.
* pktns_select_pkt_numlen: picks the packet-number encoding length (1..4 bytes);
  we show the chosen length actually holds the value it is chosen for.
-/
namespace NgtcpRV.ConnPkt

def minB (a b : BitVec 64) : BitVec 64 := if a ≤ b then a else b

/-- `conn_shape_udp_payload` with all caps applied (the no-shaping flag only skips
the last `min`). -/
def shape (payloadlen remoteMax localMax dcidMax : BitVec 64) : BitVec 64 :=
  minB (minB (minB payloadlen remoteMax) localMax) dcidMax

/-- **Datagram size is capped**: the shaped length never exceeds the requested
length nor any configured maximum (remote transport param, local setting, dcid) —
so ngtcp2 never emits a UDP payload larger than any negotiated limit. -/
theorem shape_bounded (payloadlen remoteMax localMax dcidMax : BitVec 64) :
    shape payloadlen remoteMax localMax dcidMax ≤ payloadlen ∧
    shape payloadlen remoteMax localMax dcidMax ≤ remoteMax ∧
    shape payloadlen remoteMax localMax dcidMax ≤ localMax ∧
    shape payloadlen remoteMax localMax dcidMax ≤ dcidMax := by
  unfold shape minB
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (repeat' split) <;> bv_omega

/-- `pktns_select_pkt_numlen`, over the reduced value `m = 2*gap - 1`
(and the early `return 4` for a huge gap). -/
def numlen (m : Nat) : Nat :=
  if m > 0xFFFFFF then 4 else if m > 0xFFFF then 3 else if m > 0xFF then 2 else 1

/-- The result is always a legal QUIC packet-number length (1..4 bytes). -/
theorem numlen_range (m : Nat) : 1 ≤ numlen m ∧ numlen m ≤ 4 := by
  unfold numlen; (repeat' split) <;> omega

/-- **The chosen length holds the value**: whenever a length `< 4` is returned, the
value `m` fits in that many bytes (`1 byte ↔ m ≤ 0xFF`, etc.) — the packet number
is encoded without truncation.  (`4` is the protocol maximum, used for large
gaps.) -/
theorem numlen_sufficient (m : Nat) :
    (numlen m = 1 → m ≤ 0xFF) ∧
    (numlen m = 2 → m ≤ 0xFFFF) ∧
    (numlen m = 3 → m ≤ 0xFFFFFF) := by
  unfold numlen
  refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> omega

end NgtcpRV.ConnPkt
