/-!
# conn.c Reno window increase on ACK (RFC 9002 §7.3)

`ngtcp2_cc_reno_cc_on_pkt_acked` (lib/ngtcp2_cc.c:130) grows `cwnd` when a packet is
acknowledged (outside recovery / not app-limited):

```c
  if (cstat->cwnd < cstat->ssthresh) {           /* slow start */
    cstat->cwnd += pkt->pktlen;
    return;
  }
  m = cstat->max_tx_udp_payload_size * pkt->pktlen + reno->pending_add;  /* cong. avoidance */
  reno->pending_add = m % cstat->cwnd;
  cstat->cwnd += m / cstat->cwnd;
```

We prove: `cwnd` never decreases on an ACK (slow start and congestion avoidance both
add a non-negative amount); the fractional carry `pending_add` stays strictly below
`cwnd` (so it cannot accumulate unboundedly); and the additive-increase "credit" is
exactly conserved (`(m / cwnd) * cwnd + m % cwnd = m`).
-/
namespace NgtcpRV.RenoAck

structure CA where
  cwnd : Nat
  pendingAdd : Nat

/-- Slow-start increase: `cwnd += pktlen`. -/
def ssStep (s : CA) (pktlen : Nat) : CA := { s with cwnd := s.cwnd + pktlen }

/-- Congestion-avoidance increase with fractional carry. -/
def caStep (s : CA) (maxUdp pktlen : Nat) : CA :=
  { cwnd := s.cwnd + (maxUdp * pktlen + s.pendingAdd) / s.cwnd,
    pendingAdd := (maxUdp * pktlen + s.pendingAdd) % s.cwnd }

/-- Slow start never decreases cwnd. -/
theorem ss_nondecreasing (s : CA) (pktlen : Nat) : s.cwnd ≤ (ssStep s pktlen).cwnd := by
  unfold ssStep; dsimp only; omega

/-- Congestion avoidance never decreases cwnd. -/
theorem ca_nondecreasing (s : CA) (maxUdp pktlen : Nat) : s.cwnd ≤ (caStep s maxUdp pktlen).cwnd := by
  unfold caStep; dsimp only; exact Nat.le_add_right _ _

/-- **Bounded carry**: `pending_add` stays strictly below `cwnd` (remainder of `% cwnd`),
so the fractional accumulator never grows without bound. -/
theorem pending_lt_cwnd (s : CA) (maxUdp pktlen : Nat) (h : 0 < s.cwnd) :
    (caStep s maxUdp pktlen).pendingAdd < s.cwnd := by
  unfold caStep; dsimp only; exact Nat.mod_lt _ h

/-- **Credit conservation**: the acknowledged "credit" `m` is split exactly between the
cwnd increment and the carried remainder — no bytes of increase are lost or created. -/
theorem credit_conserved (s : CA) (maxUdp pktlen : Nat) :
    ((maxUdp * pktlen + s.pendingAdd) / s.cwnd) * s.cwnd +
      (caStep s maxUdp pktlen).pendingAdd = maxUdp * pktlen + s.pendingAdd := by
  unfold caStep; dsimp only
  rw [Nat.mul_comm]; exact Nat.div_add_mod _ _

/-- cwnd is monotone non-decreasing across any sequence of slow-start ACKs. -/
def runSS (s0 : CA) (lens : List Nat) : CA := lens.foldl ssStep s0

theorem runSS_nondecreasing (s0 : CA) (lens : List Nat) : s0.cwnd ≤ (runSS s0 lens).cwnd := by
  unfold runSS
  induction lens generalizing s0 with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons]; exact Nat.le_trans (ss_nondecreasing s0 x) (ih _)

end NgtcpRV.RenoAck
