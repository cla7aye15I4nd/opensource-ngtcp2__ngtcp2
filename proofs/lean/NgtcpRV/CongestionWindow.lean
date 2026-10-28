/-!
# conn.c congestion window: the minimum-window floor is never breached

Congestion control (lib/ngtcp2_cc.c, Reno) reduces `cwnd` on a loss event but
clamps it to a minimum of two packets (RFC 9002 §7.2):

```c
  cstat->cwnd >>= NGTCP2_LOSS_REDUCTION_FACTOR_BITS;        /* halve */
  min_cwnd = 2 * cstat->max_tx_udp_payload_size;
  cstat->cwnd = ngtcp2_max(cstat->cwnd, min_cwnd);          /* floor */
  cstat->ssthresh = cstat->cwnd;
```
Persistent congestion sets `cwnd = 2 * max_tx_udp_payload_size` directly, and the
initial window is `max(2 * max_udp, 14720)`.  So `cwnd` never drops below
`2 * max_tx_udp_payload_size`.  We model the window transitions and prove the floor
invariant holds across any sequence of loss / persistent-congestion / growth
events, plus that a loss event reduces the window and keeps `ssthresh == cwnd`.
-/
namespace NgtcpRV.CongestionWindow

structure CC where
  cwnd : Nat
  ssthresh : Nat
  maxUdp : Nat

/-- The minimum congestion window `2 * max_tx_udp_payload_size`. -/
def floor (s : CC) : Nat := 2 * s.maxUdp

/-- `ngtcp2_cc_reno_cc_congestion_event`: halve then clamp to the floor; ssthresh
follows cwnd. -/
def congestionEvent (s : CC) : CC :=
  { s with cwnd := max (s.cwnd / 2) (2 * s.maxUdp), ssthresh := max (s.cwnd / 2) (2 * s.maxUdp) }

/-- `ngtcp2_cc_reno_cc_on_persistent_congestion`: drop straight to the floor. -/
def persistentCongestion (s : CC) : CC := { s with cwnd := 2 * s.maxUdp }

/-- Slow-start / congestion-avoidance growth: cwnd increases by `k`. -/
def grow (s : CC) (k : Nat) : CC := { s with cwnd := s.cwnd + k }

def Inv (s : CC) : Prop := floor s ≤ s.cwnd

inductive Op
  | loss
  | persistent
  | grow (k : Nat)

def apply (s : CC) : Op → CC
  | .loss => congestionEvent s
  | .persistent => persistentCongestion s
  | .grow k => grow s k

/-- A loss event never lowers cwnd below the floor. -/
theorem congestionEvent_floor (s : CC) : Inv (congestionEvent s) := by
  unfold Inv floor congestionEvent; simp only; omega

/-- A loss event does not increase cwnd beyond `max(old cwnd, floor)` — it reduces
(or holds at the floor). -/
theorem congestionEvent_reduces (s : CC) :
    (congestionEvent s).cwnd ≤ max s.cwnd (2 * s.maxUdp) := by
  unfold congestionEvent; simp only; omega

/-- After a loss event, `ssthresh = cwnd` (they are set to the same value). -/
theorem congestionEvent_ssthresh_eq (s : CC) :
    (congestionEvent s).ssthresh = (congestionEvent s).cwnd := rfl

/-- Persistent congestion lands exactly on the floor. -/
theorem persistentCongestion_floor (s : CC) : Inv (persistentCongestion s) := by
  unfold Inv floor persistentCongestion; simp only; omega

/-- Every transition preserves the floor invariant (growth only raises cwnd). -/
theorem apply_preserves (s : CC) (op : Op) (h : Inv s) : Inv (apply s op) := by
  cases op with
  | loss => exact congestionEvent_floor s
  | persistent => exact persistentCongestion_floor s
  | grow k =>
      unfold Inv floor at h ⊢; simp only [apply, grow]; omega

def run (s0 : CC) (ops : List Op) : CC := ops.foldl apply s0

/-- **Floor safety**: across ANY sequence of congestion-control events, `cwnd` stays
at or above `2 * max_tx_udp_payload_size`. -/
theorem run_inv (s0 : CC) (ops : List Op) (h : Inv s0) : Inv (run s0 ops) := by
  unfold run
  induction ops generalizing s0 with
  | nil => simpa using h
  | cons op ops ih =>
    simp only [List.foldl_cons]
    exact ih (apply s0 op) (apply_preserves s0 op h)

/-- The initial window `max(2*max_udp, 14720)` also satisfies the floor. -/
theorem initcwnd_floor (maxUdp ssthresh : Nat) :
    Inv ⟨max (2 * maxUdp) 14720, ssthresh, maxUdp⟩ := by
  unfold Inv floor; simp only; omega

end NgtcpRV.CongestionWindow
