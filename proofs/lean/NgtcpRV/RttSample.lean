/-!
# conn.c RTT estimation: `ngtcp2_conn_update_rtt` (RFC 9002 §5)

`ngtcp2_conn_update_rtt` (lib/ngtcp2_conn.c) folds each RTT sample into the
estimators:

```c
  cstat->latest_rtt = rtt;
  cstat->min_rtt = ngtcp2_min(cstat->min_rtt, rtt);
  if (rtt >= cstat->min_rtt + ack_delay) rtt -= ack_delay;
  cstat->rttvar = (cstat->rttvar * 3 + |smoothed_rtt - rtt|) / 4;
  cstat->smoothed_rtt = (cstat->smoothed_rtt * 7 + rtt) / 8;
```

Three facts matter for correctness/safety: `min_rtt` is monotonically
non-increasing (so the loss-detection floor only tightens); the `rtt -= ack_delay`
subtraction never underflows (it is guarded by `rtt >= min_rtt + ack_delay`); and
the `smoothed_rtt` EWMA stays between the old estimate and the new sample.
-/
namespace NgtcpRV.RttSample

structure Rtt where
  minRtt : Nat
  smoothedRtt : Nat
  rttvar : Nat
  latestRtt : Nat

/-- First sample initialises every estimator from `rtt`. -/
def firstSample (rtt : Nat) : Rtt := ⟨rtt, rtt, rtt / 2, rtt⟩

/-- The ack-delay-adjusted sample used for the EWMAs (updated `min_rtt` first). -/
def adjusted (s : Rtt) (rtt ackDelay : Nat) : Nat :=
  if rtt ≥ min s.minRtt rtt + ackDelay then rtt - ackDelay else rtt

/-- Fold one accepted sample into the estimators. -/
def updateStep (s : Rtt) (rtt ackDelay : Nat) : Rtt :=
  { minRtt := min s.minRtt rtt,
    smoothedRtt := (7 * s.smoothedRtt + adjusted s rtt ackDelay) / 8,
    rttvar := (3 * s.rttvar +
      (if s.smoothedRtt < adjusted s rtt ackDelay
       then adjusted s rtt ackDelay - s.smoothedRtt
       else s.smoothedRtt - adjusted s rtt ackDelay)) / 4,
    latestRtt := rtt }

/-- `min_rtt` never increases on a sample. -/
theorem min_rtt_mono (s : Rtt) (rtt ackDelay : Nat) :
    (updateStep s rtt ackDelay).minRtt ≤ s.minRtt := by
  unfold updateStep; simp only; omega

/-- `min_rtt` is at most the current sample. -/
theorem min_rtt_le_sample (s : Rtt) (rtt ackDelay : Nat) :
    (updateStep s rtt ackDelay).minRtt ≤ rtt := by
  unfold updateStep; simp only; omega

/-- **Underflow safety**: the `rtt -= ack_delay` subtraction is guarded, so it never
wraps and the adjusted sample stays `≥ min_rtt`. -/
theorem ack_delay_sub_safe (s : Rtt) (rtt ackDelay : Nat)
    (h : rtt ≥ min s.minRtt rtt + ackDelay) :
    (rtt - ackDelay) + ackDelay = rtt ∧ rtt - ackDelay ≥ min s.minRtt rtt := by
  constructor <;> omega

/-- **EWMA bound**: the smoothed average `(7a + r) / 8` lies between the old estimate
`a` and the new sample `r`. -/
theorem ewma_in_bounds (a r : Nat) :
    min a r ≤ (7 * a + r) / 8 ∧ (7 * a + r) / 8 ≤ max a r := by
  omega

/-- The updated `smoothed_rtt` lies between the old smoothed value and the adjusted
sample. -/
theorem smoothed_rtt_in_bounds (s : Rtt) (rtt ackDelay : Nat) :
    min s.smoothedRtt (adjusted s rtt ackDelay) ≤ (updateStep s rtt ackDelay).smoothedRtt ∧
    (updateStep s rtt ackDelay).smoothedRtt ≤ max s.smoothedRtt (adjusted s rtt ackDelay) := by
  unfold updateStep; simp only; exact ewma_in_bounds _ _

/-- Fold a sequence of samples. -/
def run (s0 : Rtt) (samples : List (Nat × Nat)) : Rtt :=
  samples.foldl (fun s p => updateStep s p.1 p.2) s0

/-- **min_rtt monotonicity over a whole run**: no sequence of samples can raise
`min_rtt` above its starting value. -/
theorem run_min_rtt_mono (s0 : Rtt) (samples : List (Nat × Nat)) :
    (run s0 samples).minRtt ≤ s0.minRtt := by
  unfold run
  induction samples generalizing s0 with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (ih (updateStep s0 p.1 p.2)) (min_rtt_mono s0 p.1 p.2)

end NgtcpRV.RttSample
