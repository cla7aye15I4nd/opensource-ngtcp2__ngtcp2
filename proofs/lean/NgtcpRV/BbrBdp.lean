/-!
# conn.c BBR bandwidth-delay product and full-bandwidth detection (lib/ngtcp2_bbr.c)

`bbr_bdp_multiple` computes the BDP estimate, capped at `NGTCP2_BBR_MAX_BDP` and
floored at 1:

```c
  if (bbr->bw > NGTCP2_BBR_MAX_BDP * NGTCP2_SECONDS / bbr->min_rtt) bbr->bdp = NGTCP2_BBR_MAX_BDP;
  else bbr->bdp = ngtcp2_max(bbr->bw * bbr->min_rtt / NGTCP2_SECONDS, 1);
  return bbr->bdp * gain_h / 100;
```

`bbr_check_full_bw_reached` latches `full_bw_reached` after three consecutive rounds
without a 25% bandwidth increase:

```c
  if (delivery_rate * 100 >= bbr->full_bw * 125) { reset; bbr->full_bw = delivery_rate; return; }
  ++bbr->full_bw_count;
  bbr->full_bw_now = bbr->full_bw_count >= 3;
  if (bbr->full_bw_now) bbr->full_bw_reached = 1;
```

We prove the BDP estimate is always at least 1 (BBR never collapses the pipe estimate
to zero), and that STARTUP exit requires exactly the three-round plateau: a ≥25% gain
resets the counter, otherwise it increments and `full_bw` is declared only at count ≥ 3.
-/
namespace NgtcpRV.BbrBdp

/-- BDP estimate before the gain multiply: capped at `maxBdp`, floored at 1. -/
def bdpValue (bw minRtt sec maxBdp : Nat) : Nat :=
  if bw > maxBdp * sec / minRtt then maxBdp else max (bw * minRtt / sec) 1

/-- **BDP floor**: the BDP estimate is always at least 1 (given a nonzero max). -/
theorem bdp_ge_1 (bw minRtt sec maxBdp : Nat) (hm : 1 ≤ maxBdp) :
    1 ≤ bdpValue bw minRtt sec maxBdp := by
  unfold bdpValue; split <;> omega

/-- `bbr_check_full_bw_reached`: returns the new `(full_bw_count, full_bw_now)`. -/
def checkFullBw (fullBwCount fullBw deliveryRate : Nat) : Nat × Bool :=
  if deliveryRate * 100 ≥ fullBw * 125 then (0, false)
  else (fullBwCount + 1, decide (fullBwCount + 1 ≥ 3))

/-- A ≥25% bandwidth gain resets the plateau counter (progress continues). -/
theorem gain_resets (fullBwCount fullBw deliveryRate : Nat)
    (h : deliveryRate * 100 ≥ fullBw * 125) :
    checkFullBw fullBwCount fullBw deliveryRate = (0, false) := by
  unfold checkFullBw; rw [if_pos h]

/-- **Full bandwidth needs three plateau rounds**: `full_bw_now` is set only once the
counter reaches 3 — STARTUP does not exit prematurely. -/
theorem full_bw_now_requires_3 (fullBwCount fullBw deliveryRate : Nat)
    (h : (checkFullBw fullBwCount fullBw deliveryRate).2 = true) :
    (checkFullBw fullBwCount fullBw deliveryRate).1 ≥ 3 := by
  unfold checkFullBw at *
  by_cases hc : deliveryRate * 100 ≥ fullBw * 125
  · rw [if_pos hc] at h; simp at h
  · rw [if_neg hc] at h ⊢; simp only [decide_eq_true_eq] at h; exact h

/-- Below the threshold the counter increments by exactly one each plateau round. -/
theorem plateau_increments (fullBwCount fullBw deliveryRate : Nat)
    (h : ¬ deliveryRate * 100 ≥ fullBw * 125) :
    (checkFullBw fullBwCount fullBw deliveryRate).1 = fullBwCount + 1 := by
  unfold checkFullBw; rw [if_neg h]

end NgtcpRV.BbrBdp
