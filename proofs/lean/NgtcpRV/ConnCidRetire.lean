/-!
Connection-ID retirement determination (conn.c / dcidtr.c, RFC 9000 §5.1.2).

An endpoint retires every connection ID whose sequence number is below the current
`retire_prior_to` watermark.  Since `retire_prior_to` is monotone non-decreasing
(proved in `ConnRetirePriorTo`), a CID once retired is never un-retired — the set
of retired CIDs only grows, so a retired CID is never reused.  We prove the
retirement predicate and its stability.
-/
namespace NgtcpRV.ConnCidRetire

/-- A CID with sequence `seq` is retired once `retire_prior_to` passes it. -/
def retired (seq retirePriorTo : Nat) : Bool := decide (seq < retirePriorTo)

theorem retired_iff (seq retirePriorTo : Nat) :
    retired seq retirePriorTo = true ↔ seq < retirePriorTo := by
  unfold retired; simp

/-- **Stability**: as `retire_prior_to` advances (monotone), a CID already retired
stays retired — the retired set only grows. -/
theorem retired_monotone (seq rpt1 rpt2 : Nat) (h : rpt1 ≤ rpt2)
    (hr : retired seq rpt1 = true) : retired seq rpt2 = true := by
  rw [retired_iff] at hr ⊢; omega

/-- A CID at or above the watermark is still active (not retired). -/
theorem active_above_watermark (seq retirePriorTo : Nat) (h : retirePriorTo ≤ seq) :
    retired seq retirePriorTo = false := by
  unfold retired; simp; omega

end NgtcpRV.ConnCidRetire
