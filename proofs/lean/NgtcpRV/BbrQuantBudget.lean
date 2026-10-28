/-!
# conn.c BBR quantization budget (lib/ngtcp2_bbr.c)

`bbr_quantization_budget` lifts a target inflight to a sendable budget, flooring it at
the offload budget and the minimum pipe cwnd, with extra headroom while probing up:

```c
  inflight = ngtcp2_max(inflight, bbr->offload_budget);
  inflight = ngtcp2_max(inflight, min_pipe_cwnd(cstat->max_tx_udp_payload_size));
  if (bbr->state == NGTCP2_BBR_STATE_PROBE_BW_UP) inflight += 2 * cstat->max_tx_udp_payload_size;
  return inflight;
```

We prove the returned budget is never below the requested inflight, the offload budget,
or the minimum pipe cwnd (`4 * max_udp`), and that PROBE_BW_UP adds exactly two
max-sized datagrams of headroom.
-/
namespace NgtcpRV.BbrQuantBudget

/-- `min_pipe_cwnd = 4 * max_udp`. -/
def minPipeCwnd (maxUdp : Nat) : Nat := maxUdp * 4

/-- `bbr_quantization_budget`. -/
def quantBudget (inflight offloadBudget maxUdp : Nat) (probeBwUp : Bool) : Nat :=
  let base := max (max inflight offloadBudget) (minPipeCwnd maxUdp)
  if probeBwUp then base + 2 * maxUdp else base

/-- The budget is never below the requested inflight. -/
theorem budget_ge_inflight (inflight offloadBudget maxUdp : Nat) (p : Bool) :
    inflight ≤ quantBudget inflight offloadBudget maxUdp p := by
  unfold quantBudget; dsimp only; split <;> omega

/-- The budget is never below the offload budget. -/
theorem budget_ge_offload (inflight offloadBudget maxUdp : Nat) (p : Bool) :
    offloadBudget ≤ quantBudget inflight offloadBudget maxUdp p := by
  unfold quantBudget; dsimp only; split <;> omega

/-- **Min-pipe floor**: the budget is never below `4 * max_udp`. -/
theorem budget_ge_min_pipe (inflight offloadBudget maxUdp : Nat) (p : Bool) :
    minPipeCwnd maxUdp ≤ quantBudget inflight offloadBudget maxUdp p := by
  unfold quantBudget minPipeCwnd; dsimp only; split <;> omega

/-- PROBE_BW_UP adds exactly two max-sized datagrams of headroom over the floored base. -/
theorem probe_up_headroom (inflight offloadBudget maxUdp : Nat) :
    quantBudget inflight offloadBudget maxUdp true
      = quantBudget inflight offloadBudget maxUdp false + 2 * maxUdp := rfl

end NgtcpRV.BbrQuantBudget
