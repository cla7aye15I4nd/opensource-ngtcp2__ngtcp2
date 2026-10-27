/-!
PTO backoff bound STATE-MACHINE invariant (conn.c loss detection).

The probe-timeout backoff multiplies the PTO by `1ULL << pto_count` (doubling on
each consecutive PTO).  An unbounded `pto_count` would make the shift undefined
(shift >= 64 is UB) and the timeout overflow.  ngtcp2 clamps on every increment:
`++pto_count; pto_count = ngtcp2_min(pto_count, 30);`.  We prove `pto_count <= 30`
across ANY timeout/reset history, hence `1ULL << pto_count` is always well-defined
(`pto_count < 64`) and the backoff factor is at most `2^30`.  By induction.
-/
namespace NgtcpRV.ConnPtoBackoff

structure Pto where
  ptoCount : Nat

/-- Invariant: the backoff exponent is clamped to 30. -/
def Inv (s : Pto) : Prop := s.ptoCount ≤ 30

/-- `++pto_count; pto_count = min(pto_count, 30)` on a PTO expiry. -/
def onTimeout (s : Pto) : Pto := ⟨min (s.ptoCount + 1) 30⟩
/-- Reset the backoff (on ack of new data / handshake confirm). -/
def onReset (_s : Pto) : Pto := ⟨0⟩

theorem onTimeout_inv (s : Pto) (_h : Inv s) : Inv (onTimeout s) := by
  unfold Inv onTimeout; show min (s.ptoCount + 1) 30 ≤ 30; omega

theorem onReset_inv (s : Pto) (_h : Inv s) : Inv (onReset s) := by
  unfold Inv onReset; show 0 ≤ 30; omega

inductive Op where
  | timeout
  | reset

def apply (s : Pto) : Op → Pto
  | .timeout => onTimeout s
  | .reset   => onReset s

/-- **PTO backoff is bounded (whole history)**: from a valid state, ANY sequence of
PTO timeouts and resets keeps `pto_count <= 30`.  By induction. -/
theorem seq_inv (ops : List Op) (s : Pto) (h : Inv s) : Inv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o with
    | timeout => exact onTimeout_inv s h
    | reset   => exact onReset_inv s h

/-- Therefore the backoff shift is always well-defined and bounded: `pto_count < 64`
(no undefined `1ULL << pto_count`) and the factor `2^pto_count <= 2^30`. -/
theorem backoff_welldefined (s : Pto) (h : Inv s) :
    s.ptoCount < 64 ∧ 2 ^ s.ptoCount ≤ 2 ^ 30 := by
  unfold Inv at h
  exact ⟨by omega, Nat.pow_le_pow_right (by omega) h⟩

end NgtcpRV.ConnPtoBackoff
