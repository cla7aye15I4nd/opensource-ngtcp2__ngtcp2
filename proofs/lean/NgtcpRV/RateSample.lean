/-!
# conn.c delivery rate sampler `ngtcp2_rst` (lib/ngtcp2_rst.c)

BBR's delivery-rate estimate comes from `ngtcp2_rst`:

```c
  rst->delivered += ent->pktlen;                          /* cumulative, monotone */
  rs->interval = ngtcp2_max(rs->send_elapsed, rs->ack_elapsed);
  rs->delivered = rst->delivered - rs->prior_delivered;
  if (rs->interval < cstat->min_rtt) return;
  if (!rs->interval) return;
  cstat->delivery_rate_sec = rs->delivered * NGTCP2_SECONDS / rs->interval;
```

We prove: the cumulative `delivered` counter is monotone; the sampling interval is at
least both the send- and ack-elapsed times; the per-sample delivered amount
(`delivered - prior_delivered`) never underflows (the prior snapshot is of an earlier,
smaller cumulative value); and the delivery-rate division happens only when the
interval is `>= min_rtt` and nonzero — so it never divides by zero nor over-estimates
from a sub-RTT interval.
-/
namespace NgtcpRV.RateSample

/-- `rst->delivered += ent->pktlen`. -/
def deliverAck (delivered pktlen : Nat) : Nat := delivered + pktlen

/-- The cumulative delivered counter is monotone. -/
theorem delivered_monotone (delivered pktlen : Nat) : delivered ≤ deliverAck delivered pktlen := by
  unfold deliverAck; omega

/-- `interval = max(send_elapsed, ack_elapsed)`. -/
def interval (sendElapsed ackElapsed : Nat) : Nat := max sendElapsed ackElapsed

theorem interval_ge_send (s a : Nat) : s ≤ interval s a := by unfold interval; omega
theorem interval_ge_ack (s a : Nat) : a ≤ interval s a := by unfold interval; omega

/-- **Per-sample underflow safety**: the delivered amount `delivered - prior_delivered`
is well-defined — the prior snapshot is an earlier (smaller) cumulative value. -/
theorem sample_no_underflow (current prior : Nat) (h : prior ≤ current) :
    (current - prior) + prior = current := by omega

/-- The delivery-rate update guard: interval is at least `min_rtt` and nonzero. -/
def shouldComputeRate (interval minRtt : Nat) : Bool :=
  decide (minRtt ≤ interval) && decide (interval ≠ 0)

/-- **No divide-by-zero**: the rate is computed only when the interval is nonzero. -/
theorem rate_requires_nonzero (interval minRtt : Nat)
    (h : shouldComputeRate interval minRtt = true) : interval ≠ 0 := by
  unfold shouldComputeRate at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- **At least an RTT**: the rate is computed only over an interval `>= min_rtt`, so a
sub-RTT measurement cannot over-estimate the delivery rate. -/
theorem rate_requires_min_rtt (interval minRtt : Nat)
    (h : shouldComputeRate interval minRtt = true) : minRtt ≤ interval := by
  unfold shouldComputeRate at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

end NgtcpRV.RateSample
