/-!
Congestion-window floor STATE-MACHINE invariant (cc.c).

The congestion window must never drop below `min_cwnd = 2 * max_tx_udp_payload`
so the connection can always send at least two packets (never permanently
stalls).  In ngtcp2 (reno/cubic): an ACK only grows `cwnd`; a congestion event
does `cwnd = max(cwnd >> 1, min_cwnd)` (halve, then floor); a reset sets
`cwnd = min_cwnd`.  We model this and prove `cwnd >= min_cwnd` across ANY sequence
of acks, losses and resets.  `cwnd` is a byte count modelled as `ℕ` (it never
approaches 2^64 in practice, and ℕ avoids spurious wraparound).
-/
namespace NgtcpRV.ConnCongestion

/-- Congestion-control window state. -/
structure CcState where
  cwnd : Nat
  minCwnd : Nat

/-- The floor invariant: the window is at least the minimum. -/
def CcInv (s : CcState) : Prop := s.minCwnd ≤ s.cwnd

/-- On ACK: the window only grows. -/
def onAck (s : CcState) (delta : Nat) : CcState := { s with cwnd := s.cwnd + delta }
/-- On congestion event: halve, then floor at `min_cwnd` (`ngtcp2_max`). -/
def congEvent (s : CcState) : CcState := { s with cwnd := max (s.cwnd / 2) s.minCwnd }
/-- On reset: set the window to `min_cwnd` (`2 * max_tx_udp_payload`). -/
def reset (s : CcState) : CcState := { s with cwnd := s.minCwnd }

theorem onAck_inv (s : CcState) (delta : Nat) (h : CcInv s) : CcInv (onAck s delta) := by
  unfold CcInv at h; show s.minCwnd ≤ s.cwnd + delta; omega

theorem congEvent_inv (s : CcState) (_h : CcInv s) : CcInv (congEvent s) := by
  unfold CcInv congEvent; show s.minCwnd ≤ max (s.cwnd / 2) s.minCwnd; omega

theorem reset_inv (s : CcState) (_h : CcInv s) : CcInv (reset s) := by
  show s.minCwnd ≤ s.minCwnd; omega

/-- A congestion-control event. -/
inductive Op where
  | ack (delta : Nat)
  | loss
  | reset

def apply (s : CcState) : Op → CcState
  | .ack d => onAck s d
  | .loss  => congEvent s
  | .reset => reset s

/-- **Congestion-window floor (whole state machine)**: from a state at or above
the floor, ANY sequence of acks, congestion events and resets keeps
`cwnd >= min_cwnd` — the window never collapses below two packets, so the
connection can always make progress.  By induction. -/
theorem seq_inv (ops : List Op) (s : CcState) (h : CcInv s) :
    CcInv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o with
    | ack d => exact onAck_inv s d h
    | loss  => exact congEvent_inv s h
    | reset => exact reset_inv s h

end NgtcpRV.ConnCongestion
