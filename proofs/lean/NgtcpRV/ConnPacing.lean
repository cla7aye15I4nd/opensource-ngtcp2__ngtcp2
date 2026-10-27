/-!
Packet pacing interval (conn.c / cc.c, RFC 9002 §7.7).

To avoid bursts, ngtcp2 paces packets: the inter-packet interval is proportional
to `smoothed_rtt * packet_size / cwnd`.  A larger congestion window means a
shorter pacing interval (packets go out faster), and the interval is zero only
when the window is zero.  We prove the interval is monotone non-increasing in
`cwnd`, so a growing window never slows sending.
-/
namespace NgtcpRV.ConnPacing

/-- The pacing interval: `rtt * mss / cwnd` (0 if the window is 0). -/
def pacingInterval (rtt mss cwnd : Nat) : Nat := if cwnd = 0 then 0 else rtt * mss / cwnd

/-- **Monotone in cwnd**: a larger congestion window yields a shorter (or equal)
pacing interval — growth never slows the pacing. -/
theorem pacing_monotone (rtt mss cwnd1 cwnd2 : Nat) (h1 : 0 < cwnd1) (h : cwnd1 ≤ cwnd2) :
    pacingInterval rtt mss cwnd2 ≤ pacingInterval rtt mss cwnd1 := by
  unfold pacingInterval
  have h2 : 0 < cwnd2 := by omega
  rw [if_neg (by omega), if_neg (by omega)]
  exact Nat.div_le_div_left h h1

/-- The interval never exceeds `rtt * mss` (one packet per RTT at `cwnd = 1`). -/
theorem pacing_bounded (rtt mss cwnd : Nat) (h : 0 < cwnd) :
    pacingInterval rtt mss cwnd ≤ rtt * mss := by
  unfold pacingInterval; rw [if_neg (by omega)]
  exact Nat.div_le_self _ _

end NgtcpRV.ConnPacing
