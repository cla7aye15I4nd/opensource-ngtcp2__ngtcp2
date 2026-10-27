/-!
Extended composite connection interpreter (conn.c) — 8 invariants jointly.

Extends `ConnComposite` with the stream-concurrency limit, the congestion-window
floor, and the rate-limiter token bucket, for a single connection interpreter
whose reachable states (over ANY event sequence) satisfy EIGHT safety invariants
at once.  A further step toward the dispatch loop's operational semantics.
-/
namespace NgtcpRV.ConnFullModel

structure Conn where
  rxMax : Nat
  rxLast : Nat
  txMax : Nat
  txOff : Nat
  lastPkt : Nat
  largestAcked : Nat
  bytesRecv : Nat
  bytesSent : Nat
  hsCompleted : Nat   -- 0 or 1 (modelling the COMPLETED flag)
  hsConfirmed : Nat   -- 0 or 1 (modelling the CONFIRMED flag)
  maxStreams : Nat
  streamsOpened : Nat
  cwnd : Nat
  minCwnd : Nat
  tokens : Nat
  burst : Nat

def Inv (c : Conn) : Prop :=
  c.rxLast ≤ c.rxMax ∧
  c.txOff ≤ c.txMax ∧
  c.largestAcked ≤ c.lastPkt ∧
  c.bytesSent ≤ 3 * c.bytesRecv ∧
  c.hsConfirmed ≤ c.hsCompleted ∧   -- handshake ordering: confirmed => completed
  c.streamsOpened ≤ c.maxStreams ∧
  c.minCwnd ≤ c.cwnd ∧
  c.tokens ≤ c.burst ∧
  c.hsConfirmed ≤ 1 ∧ c.hsCompleted ≤ 1

inductive Ev where
  | grantRx (m : Nat) | recvData (e : Nat) | grantTx (m : Nat) | sendData (k : Nat)
  | sendPkt | recvAck (p : Nat) | recvBytes (k : Nat) | sendBytes (k : Nat)
  | completeHs | confirmHs
  | grantStreams (m : Nat) | openStream
  | ccAck (d : Nat) | ccLoss | ccReset
  | rlUpdate (g : Nat) | rlDrain (n : Nat)

def step (c : Conn) : Ev → Conn
  | .grantRx m      => if c.rxMax < m then { c with rxMax := m } else c
  | .recvData e     => if e ≤ c.rxMax then { c with rxLast := max c.rxLast e } else c
  | .grantTx m      => if c.txMax < m then { c with txMax := m } else c
  | .sendData k     => if c.txOff + k ≤ c.txMax then { c with txOff := c.txOff + k } else c
  | .sendPkt        => { c with lastPkt := c.lastPkt + 1 }
  | .recvAck p      => if p ≤ c.lastPkt then { c with largestAcked := max c.largestAcked p } else c
  | .recvBytes k    => { c with bytesRecv := c.bytesRecv + k }
  | .sendBytes k    => if c.bytesSent + k ≤ 3 * c.bytesRecv then { c with bytesSent := c.bytesSent + k } else c
  | .completeHs     => { c with hsCompleted := 1 }
  | .confirmHs      => if c.hsCompleted = 1 then { c with hsConfirmed := 1 } else c
  | .grantStreams m => if c.maxStreams < m then { c with maxStreams := m } else c
  | .openStream     => if c.streamsOpened < c.maxStreams then { c with streamsOpened := c.streamsOpened + 1 } else c
  | .ccAck d        => { c with cwnd := c.cwnd + d }
  | .ccLoss         => { c with cwnd := max (c.cwnd / 2) c.minCwnd }
  | .ccReset        => { c with cwnd := c.minCwnd }
  | .rlUpdate g     => if g < c.burst ∧ c.tokens < c.burst - g then { c with tokens := c.tokens + g } else { c with tokens := c.burst }
  | .rlDrain n      => if c.tokens < n then c else { c with tokens := c.tokens - n }

theorem step_inv (c : Conn) (e : Ev) (h : Inv c) : Inv (step c e) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  cases e <;> simp only [step] <;> (repeat' split) <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (first | (simp only []; omega) | omega)

/-- **Extended composite safety**: from a state satisfying the full 8-part
invariant, ANY sequence of dispatch events leaves all eight sub-invariants intact
simultaneously.  By induction. -/
theorem seq_inv (evs : List Ev) (c : Conn) (h : Inv c) : Inv (evs.foldl step c) := by
  induction evs generalizing c with
  | nil => exact h
  | cons e es ih => exact ih _ (step_inv c e h)

end NgtcpRV.ConnFullModel
