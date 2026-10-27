/-!
Connection-state terminality invariant (conn.c).

ngtcp2's connection state (NGTCP2_CS_*) advances through the handshake
(INITIAL → WAIT_HANDSHAKE → POST_HANDSHAKE) and then may enter the terminal
teardown states CLOSING / DRAINING.  Teardown is irreversible: a closing or
draining connection never returns to an active state (it only sends a
CONNECTION_CLOSE or silently drains).  We model the state and prove that
"terminal" is monotone — once CLOSING/DRAINING, always terminal — across ANY
transition history.  By induction.
-/
namespace NgtcpRV.ConnStateMachine

inductive ConnState where
  | initial
  | waitHandshake
  | postHandshake
  | closing
  | draining
deriving DecidableEq

/-- Terminal teardown states. -/
def isTerminal : ConnState → Bool
  | .closing  => true
  | .draining => true
  | _         => false

inductive Op where
  | advance   -- handshake progress
  | close     -- enter CLOSING (immediate close)
  | drain     -- enter DRAINING (peer closed)

/-- State transition.  From a terminal state, `advance` is a no-op; `close`/`drain`
stay terminal. -/
def apply (s : ConnState) : Op → ConnState
  | .advance => match s with
    | .initial       => .waitHandshake
    | .waitHandshake => .postHandshake
    | t              => t
  | .close => match s with
    | .draining => .draining
    | _         => .closing
  | .drain => .draining

/-- Each transition preserves terminality. -/
theorem apply_terminal (s : ConnState) (o : Op) (h : isTerminal s = true) :
    isTerminal (apply s o) = true := by
  cases o <;> cases s <;> simp_all [isTerminal, apply]

/-- **Teardown is irreversible (whole state machine)**: from a terminal state, ANY
sequence of transitions stays terminal — a closing or draining connection never
returns to an active state, for any history.  By induction. -/
theorem seq_terminal (ops : List Op) (s : ConnState) (h : isTerminal s = true) :
    isTerminal (ops.foldl apply s) = true := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih => exact ih _ (apply_terminal s o h)

/-- `close` and `drain` always reach a terminal state, from any state. -/
theorem close_terminal (s : ConnState) : isTerminal (apply s .close) = true := by
  cases s <;> simp [isTerminal, apply]

theorem drain_terminal (s : ConnState) : isTerminal (apply s .drain) = true := by
  simp [isTerminal, apply]

end NgtcpRV.ConnStateMachine
