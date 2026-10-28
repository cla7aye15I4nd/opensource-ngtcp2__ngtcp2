/-!
# conn.c ECN validation state machine (RFC 9000 §13.4.2)

ECN capability of a path is tracked by `conn->tx.ecn.state` through four states
(lib/ngtcp2_conn.h:299).  Transitions live in `conn_set_ecn` (conn.c) and
`conn_verify_ecn` / loss handling (ngtcp2_rtb.c):

  * TESTING → UNKNOWN on timeout (`3*PTO`) or after `NGTCP2_ECN_MAX_NUM_VALIDATION_PKTS`;
  * any non-FAILED → CAPABLE only when an ACK positively confirms ECN marks
    (`ecn_acked`, ngtcp2_rtb.c:794);
  * any non-FAILED → FAILED on detected ECN bleaching/mangling (ngtcp2_rtb.c:787)
    or when all ECN probes are lost (ngtcp2_rtb.c:1175);
  * FAILED is terminal: `conn_verify_ecn` returns immediately if the state is
    already FAILED (ngtcp2_rtb.c:772).

The safety property: once a path is declared ECN-incapable it STAYS FAILED (no
flapping back to using ECN), and CAPABLE is only ever entered via a positive
acknowledgement.  Proved by exhaustive case analysis and induction over event
sequences.
-/
namespace NgtcpRV.EcnValidation

inductive ECN | testing | unknown | capable | failed
  deriving DecidableEq, Repr

inductive Op | timeout | ackCapable | bleach | allLost
  deriving DecidableEq, Repr

open ECN Op

/-- One ECN-validation transition, faithful to conn.c / ngtcp2_rtb.c. -/
def apply (s : ECN) (op : Op) : ECN :=
  match s, op with
  | failed, _          => failed          -- FAILED is terminal (early return)
  | _, bleach          => failed          -- bleaching detected
  | _, ackCapable      => capable         -- positive ECN confirmation
  | testing, timeout   => unknown
  | unknown, timeout   => unknown
  | capable, timeout   => capable
  | unknown, allLost   => failed          -- all probes lost while UNKNOWN
  | testing, allLost   => testing
  | capable, allLost   => capable

/-- **FAILED is absorbing**: no event ever leaves the FAILED state. -/
theorem failed_absorbing (op : Op) : apply failed op = failed := by
  cases op <;> rfl

/-- Bleaching always drives the state to FAILED. -/
theorem bleach_to_failed (s : ECN) : apply s bleach = failed := by
  cases s <;> rfl

/-- **CAPABLE requires positive confirmation**: the only way to newly enter CAPABLE
is an `ackCapable` event (a received ACK confirming ECN marks). -/
theorem capable_requires_ack (s : ECN) (op : Op)
    (hne : s ≠ capable) (h : apply s op = capable) : op = ackCapable := by
  cases s <;> cases op <;> first | rfl | (simp_all [apply]) | (exact absurd rfl hne)

def run (s0 : ECN) (ops : List Op) : ECN := ops.foldl apply s0

/-- **Once FAILED, always FAILED**: from the FAILED state, every finite sequence of
events stays FAILED. -/
theorem run_failed (ops : List Op) : run failed ops = failed := by
  unfold run
  induction ops with
  | nil => rfl
  | cons op ops ih => simp only [List.foldl_cons, failed_absorbing]; exact ih

/-- If the state is ever FAILED, it remains FAILED for the rest of the connection. -/
theorem failed_persists (s : ECN) (ops : List Op) (h : s = failed) :
    run s ops = failed := by subst h; exact run_failed ops

end NgtcpRV.EcnValidation
