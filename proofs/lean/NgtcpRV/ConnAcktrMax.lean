/-!
ACK-tracker largest-received monotonicity (acktr.c).

`ngtcp2_acktr_add` tracks the largest received packet number:
`if (acktr->max_pkt_num < pkt_num) acktr->max_pkt_num = pkt_num;` (starting at
-1).  This value drives ACK generation, so it must be monotone and must bound
every packet actually received (otherwise an ACK could under-report).  We prove,
over ANY sequence of received packet numbers: `max_pkt_num` never decreases and is
>= every received packet number.  By induction.  (`int64_t`, modelled as `ℤ`.)
-/
namespace NgtcpRV.ConnAcktrMax

/-- `acktr->max_pkt_num` update on receiving `p`: keep the larger. -/
def recvPkt (m p : Int) : Int := if m < p then p else m

/-- Process a sequence of received packet numbers. -/
def processAll (m : Int) (ps : List Int) : Int := ps.foldl recvPkt m

/-- One update never decreases the tracked maximum. -/
theorem recvPkt_ge (m p : Int) : m ≤ recvPkt m p := by
  unfold recvPkt; split <;> omega

/-- **Monotonicity**: across any received-packet history, `max_pkt_num` never
decreases. -/
theorem process_monotone (m : Int) (ps : List Int) : m ≤ processAll m ps := by
  unfold processAll
  induction ps generalizing m with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (recvPkt_ge m p) (ih (recvPkt m p))

/-- **Upper bound**: `max_pkt_num` is >= every packet number actually received, so
the tracked largest never under-reports.  By induction. -/
theorem process_ge_all (m : Int) (ps : List Int) :
    ∀ p ∈ ps, p ≤ processAll m ps := by
  induction ps generalizing m with
  | nil => intro p hp; simp at hp
  | cons q ps ih =>
    intro p hp
    simp only [List.mem_cons] at hp
    unfold processAll
    simp only [List.foldl_cons]
    rcases hp with rfl | hp
    · -- p = q: after recvPkt m p we have >= p, and later folds only increase
      have h1 : p ≤ recvPkt m p := by unfold recvPkt; split <;> omega
      exact Int.le_trans h1 (process_monotone (recvPkt m p) ps)
    · -- p in tail: IH on the updated accumulator
      exact ih (recvPkt m q) p hp

end NgtcpRV.ConnAcktrMax
