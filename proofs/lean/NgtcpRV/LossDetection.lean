/-!
# conn.c packet loss detection (RFC 9002 §6.1)

`rtb_pkt_lost` / `compute_pkt_loss_delay` (lib/ngtcp2_rtb.c) declare a packet lost
by a time threshold or a packet-reordering threshold:

```c
  loss_delay = ngtcp2_max(latest_rtt, smoothed_rtt) * 9 / 8;   /* kTimeThreshold = 9/8 */
  loss_delay = ngtcp2_max(loss_delay, NGTCP2_GRANULARITY);
  ...
  if (ngtcp2_tstamp_elapsed(ent->ts, loss_delay, ts) ||
      rtb->largest_acked_tx_pkt_num >= ent->hd.pkt_num + (int64_t)pkt_thres)   /* kPacketThreshold = 3 */
    return 1;                                                   /* lost */
  loss_time = (loss_time == UINT64_MAX) ? ent->ts + loss_delay
                                        : ngtcp2_min(loss_time, ent->ts + loss_delay);
```

We prove: the loss delay is never smaller than the timer granularity nor than
`9/8` of the RTT estimate (so a packet is not declared lost prematurely); the
packet threshold fires exactly on `largest_acked - pkt_num >= pkt_thres`; and the
`loss_time` update is monotone non-increasing and stays `<= ent->ts + loss_delay`
(it tracks the earliest next loss-timer deadline).
-/
namespace NgtcpRV.LossDetection

/-- `NGTCP2_GRANULARITY` (kept opaque). -/
def GRANULARITY : Nat := 1000000

/-- `compute_pkt_loss_delay`: `max(latest,smoothed) * 9/8`, floored at granularity. -/
def lossDelay (latestRtt smoothedRtt : Nat) : Nat :=
  max (max latestRtt smoothedRtt * 9 / 8) GRANULARITY

/-- Loss delay is at least the timer granularity. -/
theorem loss_delay_ge_granularity (l s : Nat) : GRANULARITY ≤ lossDelay l s := by
  unfold lossDelay; omega

/-- Loss delay is at least `9/8` of the larger RTT estimate — no premature loss. -/
theorem loss_delay_ge_time_threshold (l s : Nat) :
    max l s * 9 / 8 ≤ lossDelay l s := by unfold lossDelay; omega

/-- Packet-threshold loss (`kPacketThreshold = pkt_thres`): a packet is lost when the
largest acknowledged number is at least `pkt_thres` ahead of it (reordering limit). -/
def lostByPktThreshold (largestAcked pktNum pktThres : Int) : Prop :=
  pktNum + pktThres ≤ largestAcked

/-- The packet-threshold test is exactly the reordering-distance comparison. -/
theorem lost_by_threshold_iff (largestAcked pktNum pktThres : Int) :
    lostByPktThreshold largestAcked pktNum pktThres ↔
      pktThres ≤ largestAcked - pktNum := by
  unfold lostByPktThreshold; omega

/-- `loss_time` update: set to `ent->ts + loss_delay` if unset (sentinel), else the
min with it. -/
def updateLossTime (lossTime entTs ld maxSentinel : Nat) : Nat :=
  if lossTime = maxSentinel then entTs + ld else min lossTime (entTs + ld)

/-- The updated `loss_time` never exceeds this packet's deadline `ent->ts + loss_delay`.
-/
theorem loss_time_le_deadline (lossTime entTs ld maxSentinel : Nat) :
    updateLossTime lossTime entTs ld maxSentinel ≤ entTs + ld := by
  unfold updateLossTime; split <;> omega

/-- When already set, the `loss_time` update is monotone non-increasing (keeps the
earliest deadline). -/
theorem loss_time_monotone (lossTime entTs ld maxSentinel : Nat)
    (h : lossTime ≠ maxSentinel) :
    updateLossTime lossTime entTs ld maxSentinel ≤ lossTime := by
  unfold updateLossTime; rw [if_neg h]; omega

end NgtcpRV.LossDetection
