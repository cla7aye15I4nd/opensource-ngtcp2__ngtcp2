/-!
ECN-count monotonicity (conn.c ACK/ECN validation, RFC 9000 §13.4.2).

An ACK frame may carry ECN counters (ECT(0), ECT(1), CE).  Per RFC 9000 these
counts are cumulative and must never decrease; ngtcp2 validates each ACK's counts
against the previously recorded ones and rejects (ignores) an ACK whose counts
went backwards.  The invariant is that the recorded ECN counts are monotone
non-decreasing across ANY sequence of ACKs — a peer cannot manipulate congestion
response by reporting decreasing ECN counts.  By induction.
-/
namespace NgtcpRV.ConnEcn

/-- Recorded cumulative ECN counts. -/
structure Ecn where
  ect0 : Nat
  ect1 : Nat
  ce : Nat

/-- Componentwise order: `a` is below `b` on every counter. -/
def le (a b : Ecn) : Prop := a.ect0 ≤ b.ect0 ∧ a.ect1 ≤ b.ect1 ∧ a.ce ≤ b.ce

/-- Process an ACK reporting counts `(n0, n1, nce)`: accept only if none decreased
(the RFC 9000 validation), else keep the current counts. -/
def update (s : Ecn) (n0 n1 nce : Nat) : Ecn :=
  if s.ect0 ≤ n0 ∧ s.ect1 ≤ n1 ∧ s.ce ≤ nce then ⟨n0, n1, nce⟩ else s

/-- One validated update never lowers any counter. -/
theorem update_mono (s : Ecn) (n0 n1 nce : Nat) : le s (update s n0 n1 nce) := by
  unfold le update; split
  · rename_i hg; exact hg
  · exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

inductive Op where
  | ack (n0 n1 nce : Nat)

def apply (s : Ecn) : Op → Ecn
  | .ack n0 n1 nce => update s n0 n1 nce

theorem le_trans (a b c : Ecn) (h1 : le a b) (h2 : le b c) : le a c := by
  obtain ⟨x1, x2, x3⟩ := h1; obtain ⟨y1, y2, y3⟩ := h2
  exact ⟨Nat.le_trans x1 y1, Nat.le_trans x2 y2, Nat.le_trans x3 y3⟩

/-- **ECN monotonicity (whole history)**: the recorded ECN counts after ANY
sequence of ACKs are `>=` the starting counts on every counter — ngtcp2 never
lets the cumulative ECN counts decrease.  By induction. -/
theorem seq_mono (ops : List Op) (s : Ecn) : le s (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | cons o os ih =>
    cases o with
    | ack n0 n1 nce =>
      exact le_trans s (apply s (.ack n0 n1 nce)) _ (update_mono s n0 n1 nce) (ih _)

end NgtcpRV.ConnEcn
