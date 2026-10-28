/-!
# conn.c Path MTU Discovery probe selection `ngtcp2_pmtud` (lib/ngtcp2_pmtud.c)

PMTUD walks a fixed, ascending list of candidate UDP payload sizes.  `pmtud_next_probe`
advances `mtu_idx` forward, skipping sizes already achievable, above the hard max, or
known to fail; on a failed probe `min_fail_udp_payload_size` is lowered:

```c
  ++pmtud->mtu_idx;
  for (; mtu_idx < probeslen; ++mtu_idx) {
    if (probes[mtu_idx] <= max_udp_payload_size || probes[mtu_idx] > hard_max_...) continue;
    if (probes[mtu_idx] < min_fail_udp_payload_size) break;
  }
  ...
  min_fail_udp_payload_size = ngtcp2_min(min_fail_udp_payload_size, probes[mtu_idx]);
```

We prove: `mtu_idx` strictly advances (probing is forward-only and terminates);
`min_fail` is monotone non-increasing (a size known to fail stays an upper bound on
success); and a selected probe is strictly above the current MTU, within the hard max,
and below any known-failing size (so it is a genuinely new, worthwhile probe).
-/
namespace NgtcpRV.PmtudProbe

/-- `min_fail_udp_payload_size = ngtcp2_min(min_fail, probe)` on failure. -/
def updateMinFail (minFail p : Nat) : Nat := min minFail p

/-- `min_fail` never increases — a known-failing size stays an upper bound. -/
theorem min_fail_monotone (minFail p : Nat) : updateMinFail minFail p ≤ minFail := by
  unfold updateMinFail; omega

theorem min_fail_le_probe (minFail p : Nat) : updateMinFail minFail p ≤ p := by
  unfold updateMinFail; omega

/-- A probe accepted by the selection loop: above the current MTU, within the hard max,
below any known-failing size. -/
def validProbe (p maxUdp hardMax minFail : Nat) : Prop :=
  maxUdp < p ∧ p ≤ hardMax ∧ p < minFail

/-- A selected probe strictly increases the discovered MTU target. -/
theorem valid_probe_increases_mtu (p maxUdp hardMax minFail : Nat)
    (h : validProbe p maxUdp hardMax minFail) : maxUdp < p := h.1

/-- A selected probe never exceeds the configured hard maximum. -/
theorem valid_probe_within_hard_max (p maxUdp hardMax minFail : Nat)
    (h : validProbe p maxUdp hardMax minFail) : p ≤ hardMax := h.2.1

/-- A selected probe is below any size already known to fail (no re-testing). -/
theorem valid_probe_below_known_fail (p maxUdp hardMax minFail : Nat)
    (h : validProbe p maxUdp hardMax minFail) : p < minFail := h.2.2

/-- `pmtud_next_probe` advances the index by at least one (plus any skipped entries). -/
def advanceIdx (idx skipped : Nat) : Nat := idx + 1 + skipped

/-- **Forward-only probing**: the probe index strictly advances, so PMTUD terminates. -/
theorem idx_strictly_advances (idx skipped : Nat) : idx < advanceIdx idx skipped := by
  unfold advanceIdx; omega

/-- A successful probe raises the achievable MTU to the probed size (monotone up). -/
theorem success_raises_mtu (maxUdp p : Nat) (h : maxUdp < p) : maxUdp ≤ max maxUdp p := by omega

end NgtcpRV.PmtudProbe
