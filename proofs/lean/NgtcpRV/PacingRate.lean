/-!
# conn.c pacing rate and congestion-recovery predicate (ngtcp2_cc.c)

`set_pacing_rate` (lib/ngtcp2_cc.c) derives the pacing interval and send quantum and
clamps both:

```c
  cstat->pacing_interval_m = (rtt << 10) * 100 / pacing_gain_h / cstat->cwnd;
  cstat->pacing_interval_m = ngtcp2_max(cstat->pacing_interval_m, 1);   /* >= 1 */
  send_quantum = ngtcp2_min(64*1024, (NGTCP2_MILLISECONDS << 10) / pacing_interval_m);
  cstat->send_quantum = ngtcp2_max(send_quantum, 10 * cstat->max_tx_udp_payload_size);
```

`in_congestion_recovery` (line 124) decides whether a loss falls in the current
recovery period:

```c
  return cstat->congestion_recovery_start_ts != UINT64_MAX &&
         sent_time <= cstat->congestion_recovery_start_ts;
```
and persistent congestion resets `congestion_recovery_start_ts = UINT64_MAX`.

We prove the clamps give their bounds — `pacing_interval_m >= 1` (so the later
division by it cannot divide by zero) and `send_quantum >= 10 * max_udp` — and that
resetting the recovery timestamp to the sentinel leaves `in_congestion_recovery`
false.
-/
namespace NgtcpRV.PacingRate

/-- `pacing_interval_m` after the `max(_, 1)` clamp. -/
def pacingInterval (raw : Nat) : Nat := max raw 1

/-- **Divide-by-zero safety**: the clamped pacing interval is at least 1, so the
subsequent `(NGTCP2_MILLISECONDS << 10) / pacing_interval_m` never divides by zero.
-/
theorem pacing_interval_pos (raw : Nat) : 1 ≤ pacingInterval raw := by
  unfold pacingInterval; omega

/-- `send_quantum` after `max(min(64KB, …), 10 * max_udp)`. -/
def sendQuantum (q maxUdp : Nat) : Nat := max (min (64 * 1024) q) (10 * maxUdp)

/-- **send_quantum floor**: at least ten max-sized datagrams. -/
theorem send_quantum_floor (q maxUdp : Nat) : 10 * maxUdp ≤ sendQuantum q maxUdp := by
  unfold sendQuantum; omega

/-- **send_quantum ceiling**: bounded by `max(64KB, 10 * max_udp)`. -/
theorem send_quantum_ub (q maxUdp : Nat) : sendQuantum q maxUdp ≤ max (64 * 1024) (10 * maxUdp) := by
  unfold sendQuantum; omega

/-- `in_congestion_recovery`: the recovery timestamp is set and the packet was sent
no later than it.  `MAX` is the `UINT64_MAX` sentinel ("not in recovery"). -/
def inRecovery (recoveryStart sentTime maxSentinel : Nat) : Prop :=
  recoveryStart ≠ maxSentinel ∧ sentTime ≤ recoveryStart

/-- Resetting the recovery timestamp to the sentinel (persistent congestion) makes
`in_congestion_recovery` false for every packet. -/
theorem reset_exits_recovery (sentTime maxSentinel : Nat) :
    ¬ inRecovery maxSentinel sentTime maxSentinel := by
  unfold inRecovery; rintro ⟨hne, _⟩; exact hne rfl

/-- A packet sent strictly after the recovery start is not in recovery (so a fresh
loss can open a new congestion episode). -/
theorem later_not_in_recovery (recoveryStart sentTime maxSentinel : Nat)
    (h : recoveryStart < sentTime) : ¬ inRecovery recoveryStart sentTime maxSentinel := by
  unfold inRecovery; rintro ⟨_, hle⟩; omega

end NgtcpRV.PacingRate
