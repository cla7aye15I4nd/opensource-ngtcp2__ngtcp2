/-!
RTT smoothing bound (conn.c / rtb.c, RFC 9002 §5.3).

The smoothed RTT is updated as a weighted average
`smoothed_rtt = 7/8 * smoothed_rtt + 1/8 * latest_rtt`.  As a convex combination,
the new value always lies between the old estimate and the new sample — the
estimator can never jump outside the range of its inputs (so a single RTT sample
cannot drive the estimate arbitrarily high or low).  We prove the integer form
`(7*old + sample)/8` stays within `[min old sample, max old sample]`.
-/
namespace NgtcpRV.ConnRttSmooth

/-- The smoothed-RTT update: `7/8` old plus `1/8` sample (integer arithmetic). -/
def smooth (old sample : Nat) : Nat := (7 * old + sample) / 8

/-- **Within range**: the updated smoothed RTT is between the old estimate and the
new sample — a weighted average never escapes the range of its inputs. -/
theorem smooth_in_range (old sample : Nat) :
    min old sample ≤ smooth old sample ∧ smooth old sample ≤ max old sample := by
  unfold smooth; omega

/-- A sample equal to the current estimate leaves it unchanged (fixed point). -/
theorem smooth_fixed (v : Nat) : smooth v v = v := by
  unfold smooth; omega

end NgtcpRV.ConnRttSmooth
