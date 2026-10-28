/-!
# conn.c BBR min-RTT tracking `bbr_update_min_rtt` (lib/ngtcp2_bbr.c)

```c
  bbr->probe_rtt_expired = ts > bbr->probe_rtt_min_stamp + NGTCP2_BBR_PROBE_RTT_INTERVAL;
  if (ack->rtt != UINT64_MAX && (ack->rtt < bbr->probe_rtt_min_delay || bbr->probe_rtt_expired)) {
    bbr->probe_rtt_min_delay = ack->rtt; bbr->probe_rtt_min_stamp = ts;
  }
  min_rtt_expired = ts > bbr->min_rtt_stamp + NGTCP2_BBR_MIN_RTT_FILTERLEN;
  if (bbr->probe_rtt_min_delay < bbr->min_rtt || min_rtt_expired) {
    bbr->min_rtt = bbr->probe_rtt_min_delay; bbr->min_rtt_stamp = bbr->probe_rtt_min_stamp;
  }
```

Within the filter window (nothing expired), both estimates are *windowed minima*: a new
RTT sample lowers `probe_rtt_min_delay` only when it is smaller, and `min_rtt` drops to
`probe_rtt_min_delay` only when that is smaller.  On expiry the estimate refreshes
upward (the windowing).  We prove the in-window non-increasing behaviour and that the
`min_rtt` update is exactly `min(min_rtt, probe_rtt_min_delay)` in window.
-/
namespace NgtcpRV.BbrMinRtt

/-- `probe_rtt_min_delay` update: take `rtt` when it is valid and (smaller or expired). -/
def updateProbeMin (probeMin rtt : Nat) (rttValid expired : Bool) : Nat :=
  if rttValid && (decide (rtt < probeMin) || expired) then rtt else probeMin

/-- `min_rtt` update: take `probe_rtt_min_delay` when smaller or the filter expired. -/
def updateMinRtt (minRtt probeMin : Nat) (minExpired : Bool) : Nat :=
  if decide (probeMin < minRtt) || minExpired then probeMin else minRtt

/-- **In-window, probe_rtt_min_delay never increases**: without expiry, a sample can only
lower it (windowed minimum). -/
theorem probe_min_nonincreasing (probeMin rtt : Nat) (rttValid : Bool) :
    updateProbeMin probeMin rtt rttValid false ≤ probeMin := by
  unfold updateProbeMin
  by_cases hv : rttValid = true
  · by_cases hr : rtt < probeMin
    · simp [hv, hr]; omega
    · simp [hv, hr]
  · simp [hv]

/-- **In-window, min_rtt never increases**: without expiry, it drops only to a smaller
`probe_rtt_min_delay`. -/
theorem min_rtt_nonincreasing (minRtt probeMin : Nat) :
    updateMinRtt minRtt probeMin false ≤ minRtt := by
  unfold updateMinRtt
  by_cases h : probeMin < minRtt
  · simp [h]; omega
  · simp [h]

/-- **In-window, min_rtt is the running minimum** of its old value and the probe estimate. -/
theorem min_rtt_is_min (minRtt probeMin : Nat) :
    updateMinRtt minRtt probeMin false = min minRtt probeMin := by
  unfold updateMinRtt
  by_cases h : probeMin < minRtt
  · simp [h]; omega
  · simp [h]; omega

/-- On expiry the estimate refreshes to the current probe value (even if larger),
realising the sliding window. -/
theorem min_rtt_refresh_on_expiry (minRtt probeMin : Nat) :
    updateMinRtt minRtt probeMin true = probeMin := by
  unfold updateMinRtt; simp

end NgtcpRV.BbrMinRtt
