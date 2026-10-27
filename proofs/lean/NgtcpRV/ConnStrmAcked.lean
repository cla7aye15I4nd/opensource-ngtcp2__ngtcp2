/-!
Stream completion check (strm.c `ngtcp2_strm_is_all_tx_data_acked`).

A stream's outgoing data is fully acknowledged once the acked offset reaches the
highest sent offset.  ngtcp2 checks `ack_offset >= tx.offset`.  Since the acked
offset is monotone (acks never un-ack) and bounded by what was sent, this cleanly
determines stream completion.  We prove the predicate and that a completed stream
has acked exactly what it sent.
-/
namespace NgtcpRV.ConnStrmAcked

/-- All sent data is acked once `ackedOffset >= txOffset`. -/
def allTxAcked (ackedOffset txOffset : Nat) : Bool := decide (txOffset ≤ ackedOffset)

theorem all_acked_iff (ackedOffset txOffset : Nat) :
    allTxAcked ackedOffset txOffset = true ↔ txOffset ≤ ackedOffset := by
  unfold allTxAcked; simp

/-- If data is acked beyond what was sent is impossible when the acked offset is
bounded by the send offset; then "all acked" means acked offset equals send
offset. -/
theorem complete_means_equal (ackedOffset txOffset : Nat)
    (hbound : ackedOffset ≤ txOffset) (h : allTxAcked ackedOffset txOffset = true) :
    ackedOffset = txOffset := by
  rw [all_acked_iff] at h; omega

end NgtcpRV.ConnStrmAcked
