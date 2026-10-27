/-!
Packet padding correctness (ppe.c `ngtcp2_ppe_padding_size`).

When finishing a packet, ngtcp2 pads it (a) up to a requested target `n` (capped
by the buffer capacity) and (b) to at least `min_pktlen = sample_offset +
NGTCP2_HP_SAMPLELEN`, so header protection always has its 16-byte sample.  We
prove the computed padding `len` guarantees both: the padded length reaches the
HP-sample minimum (required for header protection to be applicable) and the
capped target.
-/
namespace NgtcpRV.ConnPpePadding

/-- The padding length computed by `ngtcp2_ppe_padding_size`. -/
def paddedLen (pktlen n cap minPkt : Nat) : Nat :=
  let nn := min n cap
  let len0 := if pktlen < nn then nn - pktlen else 0
  if pktlen < minPkt then max len0 (minPkt - pktlen) else len0

/-- **HP sample guaranteed**: after padding, the packet is at least `min_pktlen`
long, so header protection always has enough bytes to sample. -/
theorem padding_meets_hp_sample (pktlen n cap minPkt : Nat) :
    minPkt ≤ pktlen + paddedLen pktlen n cap minPkt := by
  simp only [paddedLen]; (repeat' split) <;> omega

/-- **Target reached**: the padded length is at least the capped target `min n cap`. -/
theorem padding_meets_target (pktlen n cap minPkt : Nat) :
    min n cap ≤ pktlen + paddedLen pktlen n cap minPkt := by
  simp only [paddedLen]; (repeat' split) <;> omega

end NgtcpRV.ConnPpePadding
