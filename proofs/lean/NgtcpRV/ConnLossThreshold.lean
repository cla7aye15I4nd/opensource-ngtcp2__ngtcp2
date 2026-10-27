/-!
Loss-detection packet-number threshold (rtb.c, RFC 9002 §6.1.1).

A sent packet is declared lost when a later packet is acknowledged and the gap in
packet numbers reaches `kPacketThreshold = 3`: `largest_acked >= pkt_num + 3`.
Because `largest_acked` is monotone (proved in `ConnPktNum`/`ConnAcktrMax`), once a
packet crosses the loss threshold it stays lost — loss detection is stable and
never "un-declares" a lost packet.  We prove the threshold predicate and its
monotonicity.
-/
namespace NgtcpRV.ConnLossThreshold

def PACKET_THRESHOLD : Nat := 3

/-- A packet `pn` is lost (by the number threshold) once `largest_acked` is at
least `pn + 3`. -/
def isLost (pn largestAcked : Nat) : Bool := decide (pn + PACKET_THRESHOLD ≤ largestAcked)

/-- The threshold predicate, unfolded. -/
theorem isLost_iff (pn largestAcked : Nat) :
    isLost pn largestAcked = true ↔ pn + 3 ≤ largestAcked := by
  unfold isLost PACKET_THRESHOLD; simp

/-- **Stability**: as `largest_acked` advances (it is monotone), a packet already
declared lost stays lost. -/
theorem lost_monotone (pn la1 la2 : Nat) (h : la1 ≤ la2) (hl : isLost pn la1 = true) :
    isLost pn la2 = true := by
  rw [isLost_iff] at hl ⊢; omega

end NgtcpRV.ConnLossThreshold
