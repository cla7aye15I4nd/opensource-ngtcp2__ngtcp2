/-!
# conn.c BBR pacing rate `bbr_set_pacing_rate_with_gain` (lib/ngtcp2_bbr.c)

```c
  if (bbr->bw == 0) return;                                   /* no div-by-zero */
  interval_m = (NGTCP2_SECONDS << 10) * 100 * 100 / pacing_gain_h / bbr->bw / (100 - MARGIN);
  interval_m = ngtcp2_max(interval_m, 1);                      /* floor >= 1 */
  if (bbr->full_bw_reached || interval_m < cstat->pacing_interval_m)
    cstat->pacing_interval_m = interval_m;
```

with `STARTUP_PACING_GAIN_H = 277` (2.77x, aggressive) and `DRAIN_PACING_GAIN_H = 50`
(0.5x, drains the queue).  We prove the pacing interval is always `>= 1` (so the later
division by it is safe), that in STARTUP (before full bandwidth) the interval only
decreases (ramp-up), that once full bandwidth is reached it is set unconditionally, and
the ordering of the STARTUP/DRAIN gains around 100%.
-/
namespace NgtcpRV.BbrPacing

/-- STARTUP pacing gain (percent-hundredths: 277 = 2.77x). -/
def STARTUP_GAIN : Nat := 277
/-- DRAIN pacing gain (50 = 0.5x). -/
def DRAIN_GAIN : Nat := 50

/-- The computed interval after the `max(_, 1)` floor. -/
def pacingInterval (raw : Nat) : Nat := max raw 1

/-- **Pacing interval floor**: always at least 1, so the later division by the pacing
interval is safe. -/
theorem pacing_interval_ge_1 (raw : Nat) : 1 ≤ pacingInterval raw := by
  unfold pacingInterval; omega

/-- The conditional store: set when full bandwidth is reached or the new interval is
smaller. -/
def updateInterval (cur intervalM : Nat) (fullBw : Bool) : Nat :=
  if fullBw || decide (intervalM < cur) then intervalM else cur

/-- **STARTUP only decreases the interval** (monotone ramp-up of the pacing rate). -/
theorem startup_only_decreases (cur intervalM : Nat) :
    updateInterval cur intervalM false ≤ cur := by
  unfold updateInterval
  by_cases h : intervalM < cur
  · simp [h]; omega
  · simp [h]

/-- Once full bandwidth is reached, the new interval is set unconditionally. -/
theorem full_bw_sets (cur intervalM : Nat) : updateInterval cur intervalM true = intervalM := by
  unfold updateInterval; simp

/-- STARTUP paces above 100% (aggressive ramp-up). -/
theorem startup_gain_aggressive : 100 < STARTUP_GAIN := by decide

/-- DRAIN paces below 100% (drains the standing queue). -/
theorem drain_gain_conservative : DRAIN_GAIN < 100 := by decide

/-- STARTUP gain strictly exceeds DRAIN gain. -/
theorem startup_gt_drain : DRAIN_GAIN < STARTUP_GAIN := by decide

end NgtcpRV.BbrPacing
