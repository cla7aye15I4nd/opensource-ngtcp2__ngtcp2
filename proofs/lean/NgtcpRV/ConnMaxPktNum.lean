/-!
Maximum packet-number bound (pkt.h `NGTCP2_MAX_PKT_NUM`, RFC 9000 §12.3).

A QUIC packet number is at most `NGTCP2_MAX_PKT_NUM = 2^62 - 1` (it is encoded as a
varint).  When `tx.last_pkt_num` would exceed this, no further packets may be sent
on the connection.  We prove a valid packet number is a valid varint (`< 2^62`)
and that reaching the maximum forbids further increment.
-/
namespace NgtcpRV.ConnMaxPktNum

def MAX_PKT_NUM : Nat := 2 ^ 62 - 1

/-- A valid packet number fits in a varint. -/
theorem valid_pkt_num_fits (pn : Nat) (h : pn ≤ MAX_PKT_NUM) : pn < 2 ^ 62 := by
  unfold MAX_PKT_NUM at h; omega

/-- At the maximum, a further increment would exceed the valid range (so sending
must stop). -/
theorem no_increment_at_max (pn : Nat) (h : pn = MAX_PKT_NUM) : ¬ (pn + 1 ≤ MAX_PKT_NUM) := by
  unfold MAX_PKT_NUM at *; omega

end NgtcpRV.ConnMaxPktNum
