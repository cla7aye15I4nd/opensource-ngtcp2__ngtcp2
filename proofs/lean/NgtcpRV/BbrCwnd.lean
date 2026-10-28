/-!
# conn.c BBR congestion control: cwnd floor and save/restore (lib/ngtcp2_bbr.c)

BBR (ngtcp2_bbr.c) manages the congestion window with a minimum-pipe floor and a
save/restore around loss recovery and PROBE_RTT:

```c
  static uint64_t min_pipe_cwnd(size_t max_udp_payload_size) { return max_udp_payload_size * 4; }

  static void bbr_save_cwnd(bbr, cstat) {
    if (!bbr->in_loss_recovery && bbr->state != PROBE_RTT) { bbr->prior_cwnd = cstat->cwnd; return; }
    bbr->prior_cwnd = ngtcp2_max(bbr->prior_cwnd, cstat->cwnd);
  }
  static void bbr_restore_cwnd(bbr, cstat) { cstat->cwnd = ngtcp2_max(cstat->cwnd, bbr->prior_cwnd); }
  /* bbr_bound_cwnd_for_model: ngtcp2_max(inflight, min_pipe_cwnd(...)) */
```

We prove the BBR minimum window is `4 * max_udp`, that `bbr_restore_cwnd` never lowers
`cwnd`, that during recovery/PROBE_RTT `bbr_save_cwnd` only raises `prior_cwnd`, that
the model bound floors the window at `min_pipe_cwnd`, and that save-then-restore never
loses window.
-/
namespace NgtcpRV.BbrCwnd

/-- `min_pipe_cwnd = 4 * max_udp_payload_size`. -/
def minPipeCwnd (maxUdp : Nat) : Nat := maxUdp * 4

/-- `bbr_save_cwnd`. -/
def saveCwnd (priorCwnd cwnd : Nat) (recoveryOrProbe : Bool) : Nat :=
  if recoveryOrProbe then max priorCwnd cwnd else cwnd

/-- `bbr_restore_cwnd`: `cwnd := max(cwnd, prior_cwnd)`. -/
def restoreCwnd (priorCwnd cwnd : Nat) : Nat := max cwnd priorCwnd

/-- `bbr_bound_cwnd_for_model`: floor the window at `min_pipe_cwnd`. -/
def boundForModel (inflight maxUdp : Nat) : Nat := max inflight (minPipeCwnd maxUdp)

/-- **Restore never shrinks cwnd**: restoring the saved window can only raise `cwnd`. -/
theorem restore_nondecreasing (priorCwnd cwnd : Nat) : cwnd ≤ restoreCwnd priorCwnd cwnd := by
  unfold restoreCwnd; omega

/-- **Restore recovers the saved window**: `cwnd` ends at least the saved `prior_cwnd`. -/
theorem restore_ge_prior (priorCwnd cwnd : Nat) : priorCwnd ≤ restoreCwnd priorCwnd cwnd := by
  unfold restoreCwnd; omega

/-- During recovery / PROBE_RTT, `bbr_save_cwnd` only raises `prior_cwnd` (monotone). -/
theorem save_recovery_monotone (priorCwnd cwnd : Nat) :
    priorCwnd ≤ saveCwnd priorCwnd cwnd true := by
  unfold saveCwnd; simp; omega

/-- Outside recovery, `bbr_save_cwnd` captures the current window exactly. -/
theorem save_normal (priorCwnd cwnd : Nat) : saveCwnd priorCwnd cwnd false = cwnd := by
  unfold saveCwnd; simp

/-- **Model bound floor**: the window is never driven below `min_pipe_cwnd = 4*max_udp`. -/
theorem bound_for_model_floor (inflight maxUdp : Nat) :
    minPipeCwnd maxUdp ≤ boundForModel inflight maxUdp := by
  unfold boundForModel; omega

/-- **Save then restore never loses window**: after saving (in recovery) and later
restoring, `cwnd` is at least its value at save time. -/
theorem save_restore_preserves (priorCwnd cwnd laterCwnd : Nat) :
    cwnd ≤ restoreCwnd (saveCwnd priorCwnd cwnd true) laterCwnd := by
  unfold restoreCwnd saveCwnd; simp; omega

end NgtcpRV.BbrCwnd
