/-!
NEW_CONNECTION_ID `retire_prior_to` validation (conn.c, RFC 9000 §19.15).

A NEW_CONNECTION_ID frame carries `(seq, retire_prior_to)`.  `retire_prior_to`
must not exceed `seq` (an endpoint cannot be told to retire a connection ID it
has not issued), and the tracked `retire_prior_to` is monotone — a frame with a
smaller value than already seen requests no new retirement.  ngtcp2 enforces
both.  We prove, across ANY sequence of frames: the tracked `retire_prior_to`
never decreases, and every accepted value is `<= ` its own `seq`.  By induction.
-/
namespace NgtcpRV.ConnRetirePriorTo

/-- Tracked highest `retire_prior_to` requested so far. -/
structure Rpt where
  maxRpt : Nat

/-- Process a NEW_CONNECTION_ID `(seq, rpt)`: accepted only if valid
(`rpt <= seq`) and it advances the retirement watermark; otherwise ignored. -/
def recv (s : Rpt) (seq rpt : Nat) : Rpt :=
  if rpt ≤ seq ∧ s.maxRpt < rpt then ⟨rpt⟩ else s

/-- One frame never lowers the retirement watermark. -/
theorem recv_mono (s : Rpt) (seq rpt : Nat) : s.maxRpt ≤ (recv s seq rpt).maxRpt := by
  unfold recv; split
  · rename_i hg; show s.maxRpt ≤ rpt; omega
  · show s.maxRpt ≤ s.maxRpt; omega

/-- Whenever the watermark advances, the new value is `<= seq` (never retire an
unissued CID). -/
theorem recv_valid (s : Rpt) (seq rpt : Nat) (h : recv s seq rpt = ⟨rpt⟩) (hne : s.maxRpt < rpt) :
    rpt ≤ seq := by
  unfold recv at h
  split at h
  · rename_i hg; exact hg.1
  · have hm : s.maxRpt = rpt := congrArg Rpt.maxRpt h; omega

inductive Op where
  | recv (seq rpt : Nat)

def apply (s : Rpt) : Op → Rpt
  | .recv seq rpt => recv s seq rpt

/-- **retire_prior_to monotonicity (whole history)**: the tracked watermark after
ANY sequence of NEW_CONNECTION_ID frames is `>=` the starting value — retirement
requests never move backward.  By induction. -/
theorem seq_mono (ops : List Op) (s : Rpt) : s.maxRpt ≤ (ops.foldl apply s).maxRpt := by
  induction ops generalizing s with
  | nil => exact Nat.le_refl _
  | cons o os ih =>
    cases o with
    | recv seq rpt =>
      exact Nat.le_trans (recv_mono s seq rpt) (ih _)

end NgtcpRV.ConnRetirePriorTo
