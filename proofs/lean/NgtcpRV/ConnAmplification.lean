/-!
Anti-amplification STATE-MACHINE invariant (conn.c), whole-history form.

Before a path is validated, a server must not send more than 3x the bytes it has
received from that path (RFC 9000 §8.1).  ngtcp2 tracks `dcid.bytes_recv` and
`dcid.bytes_sent`, gates every send on the remaining `dcid_tx_left` budget, and
grows the allowance as more is received.  The single-step budget subtraction is
proved in `ConnFlowControl` (`tx_left_preserves`); here we prove the whole-history
invariant `bytes_sent <= 3 * bytes_recv` holds across ANY sequence of receives and
(gated) sends.  By induction.
-/
namespace NgtcpRV.ConnAmplification

/-- Per-path byte accounting on an unvalidated path. -/
structure AmpState where
  bytesRecv : Nat
  bytesSent : Nat

/-- Invariant: sent at most 3x received (the anti-amplification bound). -/
def AmpInv (s : AmpState) : Prop := s.bytesSent ≤ 3 * s.bytesRecv

/-- Receive `k` bytes from the path — raises the send allowance. -/
def recv (s : AmpState) (k : Nat) : AmpState := { s with bytesRecv := s.bytesRecv + k }

/-- Send `k` bytes — allowed only within the 3x budget (`dcid_tx_left`); an
over-budget send is not performed. -/
def send (s : AmpState) (k : Nat) : AmpState :=
  if s.bytesSent + k ≤ 3 * s.bytesRecv then { s with bytesSent := s.bytesSent + k } else s

theorem recv_inv (s : AmpState) (k : Nat) (h : AmpInv s) : AmpInv (recv s k) := by
  unfold AmpInv recv at *; show s.bytesSent ≤ 3 * (s.bytesRecv + k); omega

theorem send_inv (s : AmpState) (k : Nat) (h : AmpInv s) : AmpInv (send s k) := by
  unfold AmpInv send at *
  split
  · rename_i hc; show s.bytesSent + k ≤ 3 * s.bytesRecv; omega
  · exact h

inductive Op where
  | recv (k : Nat)
  | send (k : Nat)

def apply (s : AmpState) : Op → AmpState
  | .recv k => recv s k
  | .send k => send s k

/-- **Anti-amplification (whole state machine)**: from a valid state, ANY sequence
of receives and gated sends keeps `bytes_sent <= 3 * bytes_recv` — a server never
amplifies traffic beyond 3x to an unvalidated path, for any history.  By
induction. -/
theorem seq_inv (ops : List Op) (s : AmpState) (h : AmpInv s) :
    AmpInv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o with
    | recv k => exact recv_inv s k h
    | send k => exact send_inv s k h

end NgtcpRV.ConnAmplification
