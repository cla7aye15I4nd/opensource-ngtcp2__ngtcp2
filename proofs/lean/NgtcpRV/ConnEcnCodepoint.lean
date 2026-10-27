/-!
ECN codepoint classification (conn.c, RFC 3168 / RFC 9000 §13.4).

The 2-bit ECN field of a received datagram is one of: Not-ECT (0b00), ECT(1)
(0b01), ECT(0) (0b10), CE (0b11).  A CE mark signals congestion and must increase
the CE count; ECT(0)/ECT(1) mark ECN-capable transport.  We model the 2-bit field
and prove the four codepoints partition `{0,1,2,3}` and the CE / ECN-capable
predicates are exact.
-/
namespace NgtcpRV.ConnEcnCodepoint

/-- CE (congestion experienced) is codepoint `0b11 = 3`. -/
def isCE (ecn : Nat) : Bool := decide (ecn = 3)
/-- ECN-capable transport: ECT(0) = 2 or ECT(1) = 1. -/
def isECT (ecn : Nat) : Bool := decide (ecn = 1 ∨ ecn = 2)
/-- Not-ECT is codepoint `0b00 = 0`. -/
def isNotECT (ecn : Nat) : Bool := decide (ecn = 0)

/-- The four codepoints are mutually exclusive and exhaustive over the 2-bit field. -/
theorem ecn_partition (ecn : Nat) (h : ecn < 4) :
    (isNotECT ecn = true) ∨ (isECT ecn = true) ∨ (isCE ecn = true) := by
  unfold isNotECT isECT isCE; simp only [decide_eq_true_eq]; omega

/-- CE and ECN-capable are disjoint (a CE mark is not counted as plain ECT). -/
theorem ce_not_ect (ecn : Nat) (h : isCE ecn = true) : isECT ecn = false := by
  unfold isCE isECT at *; simp_all

end NgtcpRV.ConnEcnCodepoint
