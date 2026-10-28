/-!
# conn.c PTO computation and exponential backoff (RFC 9002 §6.2)

`compute_pto` (lib/ngtcp2_conn.c) is the Probe Timeout base:

```c
  ngtcp2_duration var = ngtcp2_max(4 * rttvar, NGTCP2_GRANULARITY);
  return smoothed_rtt + var + max_ack_delay;
```
and callers scale it by a power of two for exponential backoff, e.g. the path
validation timer `timeout * (1ULL << pv->round)` (line 5334) with `pv->round`
capped at 10 (`ngtcp2_pv_handle_entry_expiry`).

The safety-relevant facts: the PTO is never degenerate — it is always at least
`NGTCP2_GRANULARITY` (and `≥ smoothed_rtt`), so the timer cannot fire immediately
and cause a retransmission storm; it is monotone in its inputs; and the backoff is
monotone and bounded when the exponent is capped.
-/
namespace NgtcpRV.PtoCompute

/-- `NGTCP2_GRANULARITY` (timer granularity); kept opaque — results hold for its
value. -/
def GRANULARITY : Nat := 1000000

/-- `compute_pto`. -/
def computePto (smoothedRtt rttvar maxAckDelay : Nat) : Nat :=
  smoothedRtt + max (4 * rttvar) GRANULARITY + maxAckDelay

/-- **PTO floor**: the PTO is always at least the timer granularity — never zero,
so the timer cannot fire immediately. -/
theorem pto_ge_granularity (sr rttvar mad : Nat) :
    GRANULARITY ≤ computePto sr rttvar mad := by unfold computePto; omega

/-- The PTO is at least the smoothed RTT. -/
theorem pto_ge_smoothed (sr rttvar mad : Nat) : sr ≤ computePto sr rttvar mad := by
  unfold computePto; omega

/-- `compute_pto` is monotone in each input. -/
theorem pto_mono_smoothed {sr1 sr2 : Nat} (rttvar mad : Nat) (h : sr1 ≤ sr2) :
    computePto sr1 rttvar mad ≤ computePto sr2 rttvar mad := by unfold computePto; omega
theorem pto_mono_rttvar (sr : Nat) {r1 r2 : Nat} (mad : Nat) (h : r1 ≤ r2) :
    computePto sr r1 mad ≤ computePto sr r2 mad := by unfold computePto; omega
theorem pto_mono_ackdelay (sr rttvar : Nat) {m1 m2 : Nat} (h : m1 ≤ m2) :
    computePto sr rttvar m1 ≤ computePto sr rttvar m2 := by unfold computePto; omega

/-- Exponential backoff: `pto * 2^n`. -/
def backoff (pto n : Nat) : Nat := pto * 2 ^ n

/-- Backoff never shrinks the timeout. -/
theorem backoff_ge (pto n : Nat) : pto ≤ backoff pto n := by
  unfold backoff
  have h : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  calc pto = pto * 1 := by rw [Nat.mul_one]
    _ ≤ pto * 2 ^ n := Nat.mul_le_mul (Nat.le_refl pto) h

/-- Backoff is monotone in the exponent (each PTO expiry at least doubles it). -/
theorem backoff_mono (pto n : Nat) : backoff pto n ≤ backoff pto (n + 1) := by
  unfold backoff
  exact Nat.mul_le_mul (Nat.le_refl pto) (Nat.pow_le_pow_right (by decide) (by omega))

/-- With the exponent capped at 10 (`pv->round ≤ 10`), the backed-off timeout is
bounded by `pto * 1024` — no unbounded blow-up. -/
theorem backoff_round_cap (pto n : Nat) (h : n ≤ 10) : backoff pto n ≤ pto * 1024 := by
  unfold backoff
  calc pto * 2 ^ n ≤ pto * 2 ^ 10 :=
        Nat.mul_le_mul (Nat.le_refl pto) (Nat.pow_le_pow_right (by decide) h)
    _ = pto * 1024 := by rfl

end NgtcpRV.PtoCompute
