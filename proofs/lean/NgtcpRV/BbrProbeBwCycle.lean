/-!
# conn.c BBR ProbeBW cycle (lib/ngtcp2_bbr.c)

In ProbeBW, `bbr_update_probe_bw_cycle_phase` advances through four phases in a fixed
cyclic order:

```c
  DOWN   -> CRUISE   (bbr_start_probe_bw_cruise, when time to cruise)
  CRUISE -> REFILL   (via is_time_to_probe_bw)
  REFILL -> UP       (bbr_start_probe_bw_up, on round_start)
  UP     -> DOWN     (bbr_start_probe_bw_down, when time to go down)
```

All four are "in ProbeBW" states (`bbr_is_in_probe_bw_state`), and REFILL/UP are the
"probing bandwidth" phases (`bbr_is_probing_bw`, together with STARTUP).  We model the
cycle and prove it is a genuine 4-cycle (returns to start after four phase advances, and
the advance is a bijection), that every phase is a ProbeBW state, and the probing-phase
classification.
-/
namespace NgtcpRV.BbrProbeBwCycle

inductive Phase | down | cruise | refill | up
  deriving DecidableEq, Repr

open Phase

/-- The canonical next phase in the ProbeBW cycle. -/
def nextPhase : Phase → Phase
  | down => cruise
  | cruise => refill
  | refill => up
  | up => down

/-- Every ProbeBW phase is an in-ProbeBW state (`bbr_is_in_probe_bw_state`). -/
def inProbeBw (_ : Phase) : Bool := true

/-- `bbr_is_probing_bw`: REFILL and UP actively probe bandwidth. -/
def isProbing : Phase → Bool
  | refill => true
  | up => true
  | _ => false

/-- The documented per-phase transitions. -/
theorem down_to_cruise : nextPhase down = cruise := rfl
theorem cruise_to_refill : nextPhase cruise = refill := rfl
theorem refill_to_up : nextPhase refill = up := rfl
theorem up_to_down : nextPhase up = down := rfl

/-- **Proper 4-cycle**: four phase advances return to the starting phase. -/
theorem cycle_returns (p : Phase) :
    nextPhase (nextPhase (nextPhase (nextPhase p))) = p := by cases p <;> rfl

/-- The phase advance is injective (a permutation of the four phases) — no phase is
skipped or conflated. -/
theorem next_injective {p q : Phase} (h : nextPhase p = q) : p = nextPhase (nextPhase (nextPhase q)) := by
  subst h; rw [cycle_returns]

/-- Every phase stays within the ProbeBW super-state. -/
theorem all_in_probe_bw (p : Phase) : inProbeBw p = true := rfl

/-- The probing-bandwidth phases are exactly REFILL and UP. -/
theorem probing_phases :
    isProbing refill = true ∧ isProbing up = true ∧
    isProbing down = false ∧ isProbing cruise = false := by
  refine ⟨rfl, rfl, rfl, rfl⟩

end NgtcpRV.BbrProbeBwCycle
