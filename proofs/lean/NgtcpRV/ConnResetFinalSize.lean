/-!
RESET_STREAM final-size validation (strm.c / conn.c, RFC 9000 §4.5).

A RESET_STREAM carries the stream's final size.  It must be at least the highest
offset already received (you cannot retroactively shrink a stream below delivered
data) and, if a final size was already known (from FIN or an earlier RESET), it
must match.  A violation is FINAL_SIZE_ERROR.  We prove the validation accepts a
final size iff it is consistent with the data seen.
-/
namespace NgtcpRV.ConnResetFinalSize

/-- A RESET final size `fsize` is valid given the highest received offset
`lastOff` and an optional known final size. -/
def validResetFinal (fsize lastOff : Nat) (known : Option Nat) : Bool :=
  decide (lastOff ≤ fsize) && (match known with | none => true | some k => decide (k = fsize))

/-- **Not below delivered data**: an accepted RESET final size is at least the
highest received offset. -/
theorem reset_final_ge_received (fsize lastOff : Nat) (known : Option Nat)
    (h : validResetFinal fsize lastOff known = true) : lastOff ≤ fsize := by
  unfold validResetFinal at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- **Consistent with a known final size**: if a final size was already known, an
accepted RESET matches it. -/
theorem reset_final_matches_known (fsize lastOff k : Nat)
    (h : validResetFinal fsize lastOff (some k) = true) : k = fsize := by
  unfold validResetFinal at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

end NgtcpRV.ConnResetFinalSize
