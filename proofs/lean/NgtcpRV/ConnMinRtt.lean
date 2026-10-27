/-!
min_rtt tracking (conn.c / rtb.c, RFC 9002 §5.2).

`cstat->min_rtt` records the lowest RTT sample observed: `min_rtt =
min(min_rtt, latest_rtt)`.  It must be monotone non-increasing and a true lower
bound on every sample seen (it anchors the PTO and loss-detection timers, which
must not be inflated by a single large sample).  We prove both over ANY sequence
of RTT samples.  By induction.
-/
namespace NgtcpRV.ConnMinRtt

/-- Fold the `min_rtt = min(min_rtt, sample)` update over a sample sequence. -/
def processMin (m : Nat) (samples : List Nat) : Nat := samples.foldl min m

/-- One update never raises `min_rtt`. -/
theorem update_le (m s : Nat) : min m s ≤ m := by omega

/-- **Monotone non-increasing**: `min_rtt` after any sample sequence is `<=` the
starting value. -/
theorem process_le (m : Nat) (samples : List Nat) : processMin m samples ≤ m := by
  unfold processMin
  induction samples generalizing m with
  | nil => simp
  | cons s ss ih => exact Nat.le_trans (ih (min m s)) (update_le m s)

/-- **Lower bound on all samples**: `min_rtt` is `<=` every RTT sample observed. -/
theorem process_le_all (m : Nat) (samples : List Nat) :
    ∀ s ∈ samples, processMin m samples ≤ s := by
  induction samples generalizing m with
  | nil => intro s hs; simp at hs
  | cons x xs ih =>
    intro s hs
    simp only [List.mem_cons] at hs
    unfold processMin
    simp only [List.foldl_cons]
    rcases hs with rfl | hs
    · exact Nat.le_trans (process_le (min m s) xs) (by omega)
    · exact ih (min m x) s hs

end NgtcpRV.ConnMinRtt
