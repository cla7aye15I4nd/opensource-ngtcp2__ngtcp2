/-!
# conn.c ACK dispatch: cannot ack an unsent packet (lib/ngtcp2_conn.c)

`conn_recv_ack` rejects an ACK whose largest acknowledged number exceeds the largest packet
we have actually sent (conn.c:5729: `if (pktns->tx.last_pkt_num < fr->largest_ack) return
NGTCP2_ERR_PROTO`), and otherwise raises `rtb->largest_acked_tx_pkt_num`.  Modelling this
dispatch slice, we prove the invariant `largest_acked <= largest_sent` is preserved (a peer
cannot acknowledge a packet number we never emitted) and that `largest_acked` is monotone
non-decreasing, across any sequence of frames.
-/
namespace NgtcpRV.ConnDispatchAck

structure CS where
  txLargestSent : Int   -- pktns->tx.last_pkt_num
  txLargestAcked : Int  -- rtb->largest_acked_tx_pkt_num

/-- You can only have acknowledged packets you actually sent. -/
def Inv (s : CS) : Prop := s.txLargestAcked ≤ s.txLargestSent

inductive Frame
  | ack (largestAck : Int)
  | other

/-- `conn_recv_ack`: reject an ACK of an unsent packet, else raise `largest_acked`. -/
def dispatch (s : CS) : Frame → Option CS
  | .ack la => if la ≤ s.txLargestSent then some { s with txLargestAcked := max s.txLargestAcked la }
               else none
  | .other => some s

/-- Every ACK dispatch preserves `largest_acked <= largest_sent`. -/
theorem dispatch_preserves (s : CS) (f : Frame) (h : Inv s) (s' : CS)
    (hd : dispatch s f = some s') : Inv s' := by
  unfold Inv at h ⊢
  cases f with
  | ack la =>
      simp only [dispatch] at hd
      by_cases hg : la ≤ s.txLargestSent
      · rw [if_pos hg] at hd; injection hd with hd; subst hd
        show max s.txLargestAcked la ≤ s.txLargestSent; omega
      · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | other => simp only [dispatch] at hd; injection hd with hd; subst hd; exact h

/-- An accepted ACK never lowers `largest_acked` (monotone). -/
theorem ack_monotone (s : CS) (la : Int) (s' : CS) (hd : dispatch s (.ack la) = some s') :
    s.txLargestAcked ≤ s'.txLargestAcked := by
  simp only [dispatch] at hd
  by_cases hg : la ≤ s.txLargestSent
  · rw [if_pos hg] at hd; injection hd with hd; subst hd
    show s.txLargestAcked ≤ max s.txLargestAcked la; omega
  · rw [if_neg hg] at hd; exact absurd hd (by simp)

def recvPkt (s0 : CS) (frames : List Frame) : CS :=
  frames.foldl (fun s f => (dispatch s f).getD s) s0

/-- The ACK-validity invariant holds across any frame sequence. -/
theorem recvPkt_preserves (s0 : CS) (frames : List Frame) (h : Inv s0) : Inv (recvPkt s0 frames) := by
  unfold recvPkt
  induction frames generalizing s0 with
  | nil => simpa using h
  | cons f fs ih =>
    simp only [List.foldl_cons]
    refine ih _ ?_
    cases hd : dispatch s0 f with
    | none => simpa [hd] using h
    | some s' => simp only [hd, Option.getD]; exact dispatch_preserves s0 f h s' hd

end NgtcpRV.ConnDispatchAck
