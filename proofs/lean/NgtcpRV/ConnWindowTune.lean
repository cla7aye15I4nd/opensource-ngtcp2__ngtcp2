/-!
Flow-control window auto-tuning (conn.c / strm.c, RFC 9000 flow control).

When a receiver is consuming data faster than it can advertise credit, ngtcp2
grows the flow-control window (doubling it) up to a configured maximum
`max_window`.  The window must stay within `[0, max_window]` and only grow.  We
model `window' = min(2*window, max_window)` and prove the window is bounded by
`max_window` and monotone non-decreasing across ANY sequence of growth steps.
-/
namespace NgtcpRV.ConnWindowTune

/-- One auto-tuning step: double the window, capped at `max_window`. -/
def grow (window maxWindow : Nat) : Nat := min (2 * window) maxWindow

/-- **Bounded**: the grown window never exceeds `max_window`. -/
theorem grow_bounded (window maxWindow : Nat) : grow window maxWindow ≤ maxWindow := by
  unfold grow; omega

/-- **Monotone**: when the window starts within the max and is positive, growth
never shrinks it (it at least stays, since `2*window >= window`). -/
theorem grow_monotone (window maxWindow : Nat) (h : window ≤ maxWindow) :
    window ≤ grow window maxWindow := by
  unfold grow; omega

/-- Repeated growth keeps the window bounded by `max_window`. -/
theorem grows_bounded (window maxWindow : Nat) (steps : Nat) (h : window ≤ maxWindow) :
    Nat.rec window (fun _ w => grow w maxWindow) steps ≤ maxWindow := by
  induction steps with
  | zero => exact h
  | succ n ih => exact grow_bounded _ _

end NgtcpRV.ConnWindowTune
