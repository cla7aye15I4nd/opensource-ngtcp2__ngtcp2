/-!
Composite connection interpreter (conn.c), whole-history form.

The individual conn.c invariants (flow control, packet numbers, amplification,
handshake ordering, teardown) are proved separately as state machines.  This
module bundles them into ONE connection state with ONE `step` function that
processes a connection event, and proves that the CONJUNCTION of all the
invariants is maintained across ANY event sequence — a step toward the dispatch
loop's operational semantics: a single interpreter whose reachable states all
satisfy the full safety invariant.  By induction.
-/
namespace NgtcpRV.ConnComposite

/-- Bundled connection state (receive & send flow control, packet-number space,
anti-amplification counters, handshake + lifecycle flags). -/
structure Conn where
  rxMax : Nat
  rxLast : Nat
  txMax : Nat
  txOff : Nat
  lastPkt : Nat
  largestAcked : Nat
  bytesRecv : Nat
  bytesSent : Nat
  hsCompleted : Bool
  hsConfirmed : Bool
  closed : Bool

/-- The full connection safety invariant: every sub-invariant at once. -/
def Inv (c : Conn) : Prop :=
  c.rxLast ≤ c.rxMax ∧              -- receive flow control
  c.txOff ≤ c.txMax ∧              -- send flow control
  c.largestAcked ≤ c.lastPkt ∧     -- packet-number monotonicity
  c.bytesSent ≤ 3 * c.bytesRecv ∧  -- anti-amplification
  (c.hsConfirmed = true → c.hsCompleted = true)  -- handshake ordering

/-- A connection event handled by the dispatch loop. -/
inductive Ev where
  | grantRx (m : Nat)      -- peer/app raised our advertised limit
  | recvData (e : Nat)     -- received stream data ending at offset e
  | grantTx (m : Nat)      -- peer raised our send limit
  | sendData (k : Nat)     -- send up to k bytes (flow-control capped)
  | sendPkt                -- assign next packet number
  | recvAck (p : Nat)      -- ack for packet p
  | recvBytes (k : Nat)    -- received k bytes (amplification credit)
  | sendBytes (k : Nat)    -- send k bytes (amplification gated)
  | completeHs
  | confirmHs
  | close

/-- The dispatch step: apply one event's effect, each gated exactly as its
originating handler. -/
def step (c : Conn) : Ev → Conn
  | .grantRx m   => if c.rxMax < m then { c with rxMax := m } else c
  | .recvData e  => if e ≤ c.rxMax then { c with rxLast := max c.rxLast e } else c
  | .grantTx m   => if c.txMax < m then { c with txMax := m } else c
  | .sendData k  => if c.txOff + k ≤ c.txMax then { c with txOff := c.txOff + k } else c
  | .sendPkt     => { c with lastPkt := c.lastPkt + 1 }
  | .recvAck p   => if p ≤ c.lastPkt then { c with largestAcked := max c.largestAcked p } else c
  | .recvBytes k => { c with bytesRecv := c.bytesRecv + k }
  | .sendBytes k => if c.bytesSent + k ≤ 3 * c.bytesRecv then { c with bytesSent := c.bytesSent + k } else c
  | .completeHs  => { c with hsCompleted := true }
  | .confirmHs   => if c.hsCompleted then { c with hsConfirmed := true } else c
  | .close       => { c with closed := true }

/-- Each event preserves the full connection invariant.  Each event touches one
sub-state; the other four invariant conjuncts pass through unchanged (they are
projections of unchanged fields, hence definitionally the same hypothesis). -/
theorem step_inv (c : Conn) (e : Ev) (h : Inv c) : Inv (step c e) := by
  obtain ⟨hrx, htx, hpn, hamp, hhs⟩ := h
  cases e with
  | grantRx m =>
    simp only [step]; split
    · exact ⟨by show c.rxLast ≤ m; omega, htx, hpn, hamp, hhs⟩
    · exact ⟨hrx, htx, hpn, hamp, hhs⟩
  | recvData e =>
    simp only [step]; split
    · rename_i hg; exact ⟨by show max c.rxLast e ≤ c.rxMax; omega, htx, hpn, hamp, hhs⟩
    · exact ⟨hrx, htx, hpn, hamp, hhs⟩
  | grantTx m =>
    simp only [step]; split
    · exact ⟨hrx, by show c.txOff ≤ m; omega, hpn, hamp, hhs⟩
    · exact ⟨hrx, htx, hpn, hamp, hhs⟩
  | sendData k =>
    simp only [step]; split
    · rename_i hg; exact ⟨hrx, by show c.txOff + k ≤ c.txMax; omega, hpn, hamp, hhs⟩
    · exact ⟨hrx, htx, hpn, hamp, hhs⟩
  | sendPkt =>
    exact ⟨hrx, htx, by show c.largestAcked ≤ c.lastPkt + 1; omega, hamp, hhs⟩
  | recvAck p =>
    simp only [step]; split
    · rename_i hg; exact ⟨hrx, htx, by show max c.largestAcked p ≤ c.lastPkt; omega, hamp, hhs⟩
    · exact ⟨hrx, htx, hpn, hamp, hhs⟩
  | recvBytes k =>
    exact ⟨hrx, htx, hpn, by show c.bytesSent ≤ 3 * (c.bytesRecv + k); omega, hhs⟩
  | sendBytes k =>
    simp only [step]; split
    · rename_i hg; exact ⟨hrx, htx, hpn, by show c.bytesSent + k ≤ 3 * c.bytesRecv; omega, hhs⟩
    · exact ⟨hrx, htx, hpn, hamp, hhs⟩
  | completeHs =>
    exact ⟨hrx, htx, hpn, hamp, by intro _; rfl⟩
  | confirmHs =>
    simp only [step]; split
    · rename_i hg; exact ⟨hrx, htx, hpn, hamp, by intro _; exact hg⟩
    · exact ⟨hrx, htx, hpn, hamp, hhs⟩
  | close =>
    exact ⟨hrx, htx, hpn, hamp, hhs⟩

/-- **Composite connection safety (whole interpreter)**: from a state satisfying
the full invariant, ANY sequence of dispatch events leaves every sub-invariant
intact simultaneously — flow control (both directions), packet-number
monotonicity, anti-amplification, and handshake ordering all hold in every
reachable state.  By induction. -/
theorem seq_inv (evs : List Ev) (c : Conn) (h : Inv c) : Inv (evs.foldl step c) := by
  induction evs generalizing c with
  | nil => exact h
  | cons e es ih => exact ih _ (step_inv c e h)

end NgtcpRV.ConnComposite
