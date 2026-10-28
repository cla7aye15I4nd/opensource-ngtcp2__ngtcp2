/-!
# conn.c source-connection-ID pool accounting (DoS bound + underflow safety)

The local endpoint issues source connection IDs to the peer and tracks them with
two counters on `conn->scid` (lib/ngtcp2_conn.c):

  * `num_in_flight` — issued SCIDs the peer may still use; incremented when a new
    SCID is queued, guarded by `assert(NGTCP2_MAX_SCID_POOL_SIZE > num_in_flight)`
    (line 3401) so it never exceeds `NGTCP2_MAX_SCID_POOL_SIZE = 8`;
  * `num_retired` — SCIDs the peer has asked to retire; incremented on
    RETIRE_CONNECTION_ID (line 8442) and decremented when the retired SCID is
    finally removed, guarded by `assert(conn->scid.num_retired)` (line 3457).

`conn_required_num_new_connection_id` keeps issuance within the pool.  The two
safety facts: the in-flight pool is bounded (an attacker cannot force unbounded
SCID state), and the `num_retired` decrement never underflows.  Proved over any
sequence of issue / retire / gc events.
-/
namespace NgtcpRV.ScidPool

/-- `NGTCP2_MAX_SCID_POOL_SIZE`. -/
def MAX_POOL : Nat := 8

structure Scid where
  numInFlight : Nat
  numRetired : Nat

inductive Op
  | issue   -- queue a new SCID (guarded by the pool cap)
  | retire  -- peer retires one of our SCIDs
  | gc      -- remove a finally-retired SCID

def apply (s : Scid) : Op → Scid
  | .issue  => if s.numInFlight < MAX_POOL then { s with numInFlight := s.numInFlight + 1 } else s
  | .retire => { s with numRetired := s.numRetired + 1 }
  | .gc     => if 0 < s.numRetired
               then { numInFlight := s.numInFlight - 1, numRetired := s.numRetired - 1 }
               else s

/-- The pool bound: at most `NGTCP2_MAX_SCID_POOL_SIZE` SCIDs in flight. -/
def Inv (s : Scid) : Prop := s.numInFlight ≤ MAX_POOL

/-- Every event preserves the pool bound. -/
theorem apply_preserves (s : Scid) (op : Op) (h : Inv s) : Inv (apply s op) := by
  have hh : s.numInFlight ≤ MAX_POOL := h
  cases op with
  | issue =>
      unfold apply Inv
      by_cases hc : s.numInFlight < MAX_POOL
      · rw [if_pos hc]; dsimp only; omega
      · rw [if_neg hc]; omega
  | retire => unfold apply Inv; dsimp only; omega
  | gc =>
      unfold apply Inv
      by_cases hc : 0 < s.numRetired
      · rw [if_pos hc]; dsimp only; omega
      · rw [if_neg hc]; omega

/-- **gc underflow safety**: a retired-SCID removal is guarded, so `num_retired`
never wraps. -/
theorem gc_no_underflow (s : Scid) (h : 0 < s.numRetired) :
    (apply s .gc).numRetired + 1 = s.numRetired := by
  unfold apply; rw [if_pos h]; dsimp only; omega

def run (s0 : Scid) (ops : List Op) : Scid := ops.foldl apply s0

/-- **Pool bound over any event sequence**: the in-flight SCID count never exceeds
`NGTCP2_MAX_SCID_POOL_SIZE`, so SCID state stays bounded. -/
theorem run_inv (s0 : Scid) (ops : List Op) (h : Inv s0) : Inv (run s0 ops) := by
  unfold run
  induction ops generalizing s0 with
  | nil => simpa using h
  | cons op ops ih =>
    simp only [List.foldl_cons]
    exact ih (apply s0 op) (apply_preserves s0 op h)

/-- Issuing never pushes the in-flight count over the cap, even applied directly. -/
theorem issue_respects_cap (s : Scid) (h : Inv s) : (apply s .issue).numInFlight ≤ MAX_POOL :=
  apply_preserves s .issue h

end NgtcpRV.ScidPool
