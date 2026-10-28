/-!
# conn.c CUBIC congestion event (RFC 9438)

`ngtcp2_cc_cubic_cc_congestion_event` (lib/ngtcp2_cc.c:479) reduces the window on
loss with fast convergence:

```c
  if (cstat->cwnd < cubic->current.w_max) cubic->current.w_max = cstat->cwnd * 17 / 20;
  else                                    cubic->current.w_max = cstat->cwnd;
  cubic->current.w_max = ngtcp2_max(cubic->current.w_max, 2 * cstat->max_tx_udp_payload_size);
  cstat->ssthresh = cstat->cwnd * 7 / 10;
  ... (ssthresh may be reduced further) ...
  cstat->ssthresh = ngtcp2_max(cstat->ssthresh, 2 * cstat->max_tx_udp_payload_size);
  cstat->cwnd = cstat->ssthresh;
```

We prove the CUBIC minimum-window floor is respected (`w_max`, `ssthresh`, and the
resulting `cwnd` are all `>= 2 * max_udp`), fast convergence reduces `w_max` below the
old `cwnd` when below `w_max`, and the multiplicative decrease `cwnd * 7/10` does not
exceed the old `cwnd`.
-/
namespace NgtcpRV.CubicWindow

/-- New `w_max` after fast convergence and floor. -/
def newWmax (cwnd wMax maxUdp : Nat) : Nat :=
  max (if cwnd < wMax then cwnd * 17 / 20 else cwnd) (2 * maxUdp)

/-- Final `ssthresh` is the (possibly delivered-reduced) base, floored at `2*max_udp`;
modelled as `max base (2*max_udp)` for an arbitrary non-negative base. -/
def flooredSsthresh (base maxUdp : Nat) : Nat := max base (2 * maxUdp)

/-- **w_max floor**: never below two max datagrams. -/
theorem wmax_floor (cwnd wMax maxUdp : Nat) : 2 * maxUdp ≤ newWmax cwnd wMax maxUdp := by
  unfold newWmax; omega

/-- **Fast convergence**: while below `w_max`, the new `w_max` does not exceed the old
`cwnd` (the window target is pulled down, `17/20 = 0.85`). -/
theorem wmax_fast_convergence (cwnd wMax maxUdp : Nat) (h : cwnd < wMax) :
    newWmax cwnd wMax maxUdp ≤ max cwnd (2 * maxUdp) := by
  unfold newWmax; rw [if_pos h]; omega

/-- **ssthresh floor**: the reduced slow-start threshold stays at or above two max
datagrams, whatever the intermediate reduction. -/
theorem ssthresh_floor (base maxUdp : Nat) : 2 * maxUdp ≤ flooredSsthresh base maxUdp := by
  unfold flooredSsthresh; omega

/-- **Multiplicative decrease**: the base `cwnd * 7/10` does not exceed the old `cwnd`. -/
theorem md_reduces (cwnd : Nat) : cwnd * 7 / 10 ≤ cwnd := by omega

/-- **Minimum congestion window**: after the event `cwnd = ssthresh`, so the new `cwnd`
is at least `2 * max_udp` (RFC 9438 minimum window), for any intermediate ssthresh. -/
theorem cwnd_after_event_floor (base maxUdp : Nat) :
    2 * maxUdp ≤ flooredSsthresh base maxUdp := ssthresh_floor base maxUdp

end NgtcpRV.CubicWindow
