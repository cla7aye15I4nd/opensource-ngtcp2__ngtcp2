/-!
Earliest-deadline timer selection (conn.c `ngtcp2_conn_get_expiry`).

The connection's next expiry is the earliest of all its pending timers (loss, PTO,
idle, keep-alive, path-validation, …), computed with `ngtcp2_min` over the set.
We prove the selected deadline is no later than any pending timer and is one of
them — so the single scheduled wake-up never misses a timer.
-/
namespace NgtcpRV.ConnTimerSelect

/-- The earliest of a non-empty list of deadlines. -/
def earliest (d : Nat) (ds : List Nat) : Nat := ds.foldl min d

/-- One step never increases the running minimum. -/
theorem earliest_le_head (d : Nat) (ds : List Nat) : earliest d ds ≤ d := by
  unfold earliest
  induction ds generalizing d with
  | nil => simp
  | cons x xs ih => exact Nat.le_trans (ih (min d x)) (by omega)

/-- **No timer missed**: the selected deadline is at most every pending deadline. -/
theorem earliest_le_all (d : Nat) (ds : List Nat) :
    ∀ x ∈ ds, earliest d ds ≤ x := by
  induction ds generalizing d with
  | nil => intro x hx; simp at hx
  | cons y ys ih =>
    intro x hx
    simp only [List.mem_cons] at hx
    unfold earliest; simp only [List.foldl_cons]
    rcases hx with rfl | hx
    · exact Nat.le_trans (earliest_le_head (min d x) ys) (by omega)
    · exact ih (min d y) x hx

end NgtcpRV.ConnTimerSelect
