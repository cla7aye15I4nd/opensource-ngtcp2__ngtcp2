/-!
PTO lower bound (conn.c `compute_pto`, RFC 9002 §6.2.1).

The probe timeout is `smoothed_rtt + max(4*rttvar, granularity) + max_ack_delay`.
Because the variance term is at least `granularity > 0`, the PTO is always strictly
positive and at least the smoothed RTT — a probe timer is never zero or shorter
than the current RTT estimate (which would cause spurious probes).
-/
namespace NgtcpRV.ConnPtoBound

/-- `compute_pto`. -/
def computePto (smoothedRtt rttvar maxAckDelay granularity : Nat) : Nat :=
  smoothedRtt + max (4 * rttvar) granularity + maxAckDelay

/-- **At least the smoothed RTT**: the PTO is never shorter than the RTT estimate. -/
theorem pto_ge_rtt (smoothedRtt rttvar maxAckDelay granularity : Nat) :
    smoothedRtt ≤ computePto smoothedRtt rttvar maxAckDelay granularity := by
  unfold computePto; omega

/-- **Strictly positive**: with a positive timer granularity, the PTO is never
zero, so the probe timer always makes progress. -/
theorem pto_positive (smoothedRtt rttvar maxAckDelay granularity : Nat)
    (h : 0 < granularity) :
    0 < computePto smoothedRtt rttvar maxAckDelay granularity := by
  unfold computePto; omega

end NgtcpRV.ConnPtoBound
