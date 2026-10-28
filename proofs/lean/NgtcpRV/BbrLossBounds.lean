/-!
# conn.c BBR loss-response bounds (lib/ngtcp2_bbr.c)

On loss BBR tightens its short-term model with `beta = 7/10` (floored at the latest
sample) and bounds the model estimates:

```c
  bbr->bw_shortterm = ngtcp2_max(bbr->bw_latest, bbr->bw_shortterm * 7 / 10);
  bbr->inflight_shortterm = ngtcp2_max(bbr->inflight_latest, bbr->inflight_shortterm * 7 / 10);
  bbr->bw = ngtcp2_min(bbr->max_bw, bbr->bw_shortterm);                  /* bound_bw_for_model */
  return ngtcp2_min(bbr->bdp, cstat->cwnd);                             /* target_inflight */
  return rs->lost * LOSS_THRESH_DENOM > rs->tx_in_flight * LOSS_THRESH_NUMER;  /* too_high */
```

We prove: the loss-lowered short-term bound stays at least the latest sample and is a
`<=`-reduction of the old value; the model bandwidth is the min of max_bw and the
short-term bound; the target inflight is the min of bdp and cwnd; and the
inflight-too-high test is exactly the loss-fraction threshold comparison.
-/
namespace NgtcpRV.BbrLossBounds

/-- `bbr_loss_lower_bounds` for one estimate: `max(latest, value * 7/10)`. -/
def lossLower (latest value : Nat) : Nat := max latest (value * 7 / 10)

/-- The loss-lowered bound never drops below the latest sample. -/
theorem loss_lower_ge_latest (latest value : Nat) : latest ≤ lossLower latest value := by
  unfold lossLower; omega

/-- The `7/10` factor is a reduction of the old value. -/
theorem beta_reduces (value : Nat) : value * 7 / 10 ≤ value := by omega

/-- `bbr_bound_bw_for_model`: `bw = min(max_bw, bw_shortterm)`. -/
def boundBwForModel (maxBw bwShortterm : Nat) : Nat := min maxBw bwShortterm

theorem bound_bw_le_max (maxBw bwShortterm : Nat) : boundBwForModel maxBw bwShortterm ≤ maxBw := by
  unfold boundBwForModel; omega
theorem bound_bw_le_shortterm (maxBw bwShortterm : Nat) :
    boundBwForModel maxBw bwShortterm ≤ bwShortterm := by unfold boundBwForModel; omega

/-- `bbr_target_inflight = min(bdp, cwnd)`. -/
def targetInflight (bdp cwnd : Nat) : Nat := min bdp cwnd

theorem target_le_bdp (bdp cwnd : Nat) : targetInflight bdp cwnd ≤ bdp := by
  unfold targetInflight; omega
theorem target_le_cwnd (bdp cwnd : Nat) : targetInflight bdp cwnd ≤ cwnd := by
  unfold targetInflight; omega

/-- `bbr_is_inflight_too_high`: the loss count exceeds the threshold fraction of the
transmitted inflight. -/
def isInflightTooHigh (lost txInFlight numer denom : Nat) : Bool :=
  decide (lost * denom > txInFlight * numer)

/-- The too-high test is exactly the loss-fraction threshold comparison. -/
theorem too_high_iff (lost txInFlight numer denom : Nat) :
    isInflightTooHigh lost txInFlight numer denom = true ↔ lost * denom > txInFlight * numer := by
  unfold isInflightTooHigh; rw [decide_eq_true_eq]

end NgtcpRV.BbrLossBounds
