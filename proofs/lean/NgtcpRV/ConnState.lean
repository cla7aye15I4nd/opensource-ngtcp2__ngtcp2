/-!
# conn.c connection state machine: closing/draining are terminal

`ngtcp2_conn_state` (lib/ngtcp2_conn.h:60) is the top-level connection lifecycle:
handshake states (`CLIENT_INITIAL → CLIENT_WAIT_HANDSHAKE → POST_HANDSHAKE`, and the
server mirror) plus two end states `CS_CLOSING` (set when we send CONNECTION_CLOSE,
conn.c:12914/13009) and `CS_DRAINING` (set when we receive one, conn.c:6155/8145).

Once the connection enters the closing or draining period it is dead: no normal
processing returns it to an active handshake/post-handshake state (RFC 9000 §10.2).
We model the transitions and prove the terminal (closing ∨ draining) condition is
absorbing across any event sequence, and that handshake progression only moves
forward.
-/
namespace NgtcpRV.ConnState

inductive CS
  | clientInitial | clientWait | serverInitial | serverWait | postHandshake
  | closing | draining
  deriving DecidableEq, Repr

inductive Ev | advance | sendClose | recvClose
  deriving DecidableEq, Repr

open CS Ev

/-- One transition: advancing the handshake, or entering the closing / draining end
state on sending / receiving a CONNECTION_CLOSE. -/
def step (s : CS) : Ev → CS
  | sendClose => closing
  | recvClose => draining
  | advance => match s with
      | clientInitial => clientWait
      | clientWait => postHandshake
      | serverInitial => serverWait
      | serverWait => postHandshake
      | postHandshake => postHandshake
      | closing => closing
      | draining => draining

/-- The connection is in its terminal period (closing or draining). -/
def isTerminal (s : CS) : Bool := s == closing || s == draining

/-- **Terminal absorbing**: once closing or draining, every event keeps the
connection terminal — it never returns to an active state. -/
theorem terminal_absorbing (s : CS) (ev : Ev) (h : isTerminal s = true) :
    isTerminal (step s ev) = true := by
  cases s <;> cases ev <;> simp_all [isTerminal, step]

def run (s0 : CS) (evs : List Ev) : CS := evs.foldl step s0

/-- **No resurrection**: from a terminal state, every finite event sequence stays
terminal. -/
theorem run_terminal (s0 : CS) (evs : List Ev) (h : isTerminal s0 = true) :
    isTerminal (run s0 evs) = true := by
  unfold run
  induction evs generalizing s0 with
  | nil => simpa using h
  | cons ev evs ih => simp only [List.foldl_cons]; exact ih _ (terminal_absorbing s0 ev h)

/-- Handshake rank: measures forward progress (end states sit at the top). -/
def rank : CS → Nat
  | clientInitial => 0 | serverInitial => 0
  | clientWait => 1 | serverWait => 1
  | postHandshake => 2
  | closing => 3 | draining => 3

/-- Handshake advance never moves backward in rank. -/
theorem advance_forward (s : CS) : rank s ≤ rank (step s advance) := by
  cases s <;> simp [step, rank]

/-- Sending/receiving a close moves straight to a terminal state. -/
theorem close_is_terminal (s : CS) : isTerminal (step s sendClose) = true ∧ isTerminal (step s recvClose) = true := by
  constructor <;> simp [step, isTerminal]

end NgtcpRV.ConnState
