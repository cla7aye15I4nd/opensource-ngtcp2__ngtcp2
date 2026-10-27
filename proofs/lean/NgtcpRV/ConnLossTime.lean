/-!
Loss time-threshold (rtb.c, RFC 9002 §6.1.2).

Besides the packet-number threshold (`ConnLossThreshold`), a packet is declared
lost once it was sent more than `loss_delay` before the current time:
`sent_time + loss_delay <= now`.  `loss_delay = 9/8 * max(smoothed_rtt, latest_rtt)`
is positive.  Since time only advances, a packet lost by time stays lost.  We prove
the time-threshold predicate and its monotonicity.
-/
namespace NgtcpRV.ConnLossTime

/-- A packet is lost by the time threshold at `now`. -/
def lostByTime (sentTime lossDelay now : Nat) : Bool := decide (sentTime + lossDelay ≤ now)

theorem lostByTime_iff (sentTime lossDelay now : Nat) :
    lostByTime sentTime lossDelay now = true ↔ sentTime + lossDelay ≤ now := by
  unfold lostByTime; simp

/-- **Stable**: once lost by time, a packet stays lost as time advances. -/
theorem lost_stays_lost (sentTime lossDelay now1 now2 : Nat) (h : now1 ≤ now2)
    (hl : lostByTime sentTime lossDelay now1 = true) :
    lostByTime sentTime lossDelay now2 = true := by
  rw [lostByTime_iff] at hl ⊢; omega

end NgtcpRV.ConnLossTime
