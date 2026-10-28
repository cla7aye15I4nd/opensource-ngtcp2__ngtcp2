/-!
# conn.c BBR top-level state machine (lib/ngtcp2_bbr.c)

BBR's main lifecycle (`ngtcp2_bbr_state`) is STARTUP → DRAIN → PROBE_BW, with PROBE_RTT
a transient visited periodically:

```c
  bbr_enter_startup:    state = STARTUP;
  bbr_enter_drain:      state = DRAIN;             (from STARTUP, check_startup_done)
  bbr_enter_probe_bw -> bbr_start_probe_bw_down:  state = PROBE_BW_DOWN;  (from DRAIN)
  bbr_enter_probe_rtt:  state = PROBE_RTT;
  bbr_exit_probe_rtt:   full_bw_reached ? enter_probe_bw : enter_startup;
```

Collapsing the four PROBE_BW sub-phases (their cycle is proved in BbrProbeBwCycle), we
model the four coarse states and prove the forward progression STARTUP → DRAIN →
PROBE_BW, and that `bbr_exit_probe_rtt` returns to PROBE_BW exactly when full bandwidth
has been reached (so after full-bw is latched, PROBE_RTT never regresses to STARTUP).
-/
namespace NgtcpRV.BbrStateMachine

inductive St | startup | drain | probeBw | probeRtt
  deriving DecidableEq, Repr

open St

/-- `bbr_enter_drain` (from STARTUP). -/
def startupDone : St := drain
/-- `bbr_enter_probe_bw` (from DRAIN). -/
def drainDone : St := probeBw
/-- `bbr_exit_probe_rtt`: back to PROBE_BW if full bandwidth reached, else STARTUP. -/
def exitProbeRtt (fullBw : Bool) : St := if fullBw then probeBw else startup

/-- Progress rank for the main ramp (PROBE_RTT is transient, ranked with PROBE_BW). -/
def rank : St → Nat
  | startup => 0 | drain => 1 | probeBw => 2 | probeRtt => 2

/-- STARTUP advances to DRAIN. -/
theorem startup_advances : rank startup < rank startupDone := by decide
/-- DRAIN advances to PROBE_BW. -/
theorem drain_advances : rank drain < rank drainDone := by decide

/-- `bbr_exit_probe_rtt` returns to PROBE_BW once full bandwidth is reached. -/
theorem exit_probe_rtt_full_bw (h : fullBw = true) : exitProbeRtt fullBw = probeBw := by
  unfold exitProbeRtt; rw [h]; rfl

/-- Before full bandwidth, `bbr_exit_probe_rtt` restarts in STARTUP. -/
theorem exit_probe_rtt_not_full : exitProbeRtt false = startup := rfl

/-- **No STARTUP regression after full bandwidth**: once full-bw is latched, exiting
PROBE_RTT never returns to STARTUP. -/
theorem full_bw_no_startup_regression (h : fullBw = true) : exitProbeRtt fullBw ≠ startup := by
  rw [exit_probe_rtt_full_bw h]; decide

/-- The main ramp is strictly forward: STARTUP < DRAIN < PROBE_BW in rank. -/
theorem ramp_forward : rank startup < rank drain ∧ rank drain < rank probeBw := by
  refine ⟨by decide, by decide⟩

end NgtcpRV.BbrStateMachine
