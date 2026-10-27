/-!
Loss-delay granularity floor (rtb.c, RFC 9002 §6.1.2).

The time-threshold loss delay is `max(9/8 * max(smoothed_rtt, latest_rtt),
kGranularity)`, so it is never below the timer granularity `kGranularity`.  This
avoids spuriously declaring packets lost on a near-zero RTT.  We prove the loss
delay is at least the granularity and at least `9/8` of the RTT estimate.
-/
namespace NgtcpRV.ConnLossDelay

/-- `loss_delay = max(9/8 * rtt, granularity)`. -/
def lossDelay (rtt granularity : Nat) : Nat := max (9 * rtt / 8) granularity

theorem loss_delay_ge_granularity (rtt granularity : Nat) :
    granularity ≤ lossDelay rtt granularity := by unfold lossDelay; omega

theorem loss_delay_ge_rtt_factor (rtt granularity : Nat) :
    9 * rtt / 8 ≤ lossDelay rtt granularity := by unfold lossDelay; omega

/-- With positive granularity the loss delay is positive (no zero loss timer). -/
theorem loss_delay_positive (rtt granularity : Nat) (h : 0 < granularity) :
    0 < lossDelay rtt granularity := by unfold lossDelay; omega

end NgtcpRV.ConnLossDelay
