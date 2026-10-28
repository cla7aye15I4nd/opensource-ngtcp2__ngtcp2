/-!
# conn.c BBR delivery-round counting `bbr_update_round` (lib/ngtcp2_bbr.c)

```c
  if (ack->pkt_delivered >= bbr->next_round_delivered) {
    bbr_start_round(bbr);          /* next_round_delivered = rst->delivered */
    ++bbr->round_count;
    ++bbr->rounds_since_probe_up;
    bbr->round_start = 1;
    bbr->bytes_lost_in_round = 0;
    bbr->loss_events_in_round = 0;
    return;
  }
  bbr->round_start = 0;
```

A delivery round ends when the cumulative `pkt_delivered` reaches the mark captured at
round start.  We prove `round_count` is monotone (increments by exactly one per round
boundary, else unchanged), `round_start` is true iff a boundary was crossed, and the
per-round loss counters reset to zero at each boundary.
-/
namespace NgtcpRV.BbrRound

structure Round where
  roundCount : Nat
  nextRoundDelivered : Nat
  roundStart : Bool
  bytesLost : Nat

/-- `bbr_update_round`. -/
def updateRound (r : Round) (pktDelivered delivered : Nat) : Round :=
  if pktDelivered ≥ r.nextRoundDelivered then
    { roundCount := r.roundCount + 1, nextRoundDelivered := delivered,
      roundStart := true, bytesLost := 0 }
  else { r with roundStart := false }

/-- `round_count` never decreases. -/
theorem round_count_monotone (r : Round) (pktDelivered delivered : Nat) :
    r.roundCount ≤ (updateRound r pktDelivered delivered).roundCount := by
  unfold updateRound
  by_cases h : pktDelivered ≥ r.nextRoundDelivered
  · rw [if_pos h]; dsimp only; omega
  · rw [if_neg h]; exact Nat.le_refl _

/-- On a round boundary, `round_count` increments by exactly one. -/
theorem round_count_increments (r : Round) (pktDelivered delivered : Nat)
    (h : pktDelivered ≥ r.nextRoundDelivered) :
    (updateRound r pktDelivered delivered).roundCount = r.roundCount + 1 := by
  unfold updateRound; rw [if_pos h]

/-- `round_start` is set exactly when the delivery-round boundary is crossed. -/
theorem round_start_iff (r : Round) (pktDelivered delivered : Nat) :
    (updateRound r pktDelivered delivered).roundStart = true ↔
      pktDelivered ≥ r.nextRoundDelivered := by
  unfold updateRound
  by_cases h : pktDelivered ≥ r.nextRoundDelivered
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

/-- The per-round loss counter resets to zero at a round boundary. -/
theorem loss_reset_on_boundary (r : Round) (pktDelivered delivered : Nat)
    (h : pktDelivered ≥ r.nextRoundDelivered) :
    (updateRound r pktDelivered delivered).bytesLost = 0 := by
  unfold updateRound; rw [if_pos h]

/-- Over any sequence of acks, `round_count` is monotone non-decreasing. -/
def run (r0 : Round) (acks : List (Nat × Nat)) : Round :=
  acks.foldl (fun r p => updateRound r p.1 p.2) r0

theorem run_round_count_monotone (r0 : Round) (acks : List (Nat × Nat)) :
    r0.roundCount ≤ (run r0 acks).roundCount := by
  unfold run
  induction acks generalizing r0 with
  | nil => simp
  | cons p acks ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (round_count_monotone r0 p.1 p.2) (ih _)

end NgtcpRV.BbrRound
