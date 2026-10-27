/-!
Encryption-level ordering STATE-MACHINE invariant (conn.c dispatch).

QUIC uses increasing encryption levels — Initial (0), Handshake (1), 1-RTT (2);
a packet at a level can only be processed once the keys for that level are
installed (RFC 9001).  The dispatch loop installs keys as the handshake
progresses (levels only advance) and rejects a packet whose level exceeds the
installed level.  The invariant is `maxAcceptedLevel <= currentLevel`: ngtcp2
never processes a packet before the corresponding keys exist (e.g. no 1-RTT
packet before the handshake installs 1-RTT keys).  Proved across ANY history.
-/
namespace NgtcpRV.ConnCryptoLevel

/-- Dispatch crypto-level state: highest installed key level, highest accepted
packet level. -/
structure LvlState where
  currentLevel : Nat     -- highest encryption level whose keys are installed
  maxAccepted : Nat      -- highest packet level processed so far

def LvlInv (s : LvlState) : Prop := s.maxAccepted ≤ s.currentLevel

/-- Install keys up to level `l` (levels only advance). -/
def installKeys (s : LvlState) (l : Nat) : LvlState :=
  { s with currentLevel := max s.currentLevel l }

/-- Process a packet at level `l`; accepted only if its keys are installed
(`l <= currentLevel`), else dropped. -/
def acceptPkt (s : LvlState) (l : Nat) : LvlState :=
  if l ≤ s.currentLevel then { s with maxAccepted := max s.maxAccepted l } else s

theorem installKeys_inv (s : LvlState) (l : Nat) (h : LvlInv s) : LvlInv (installKeys s l) := by
  unfold LvlInv installKeys at *; simp only []; omega

theorem acceptPkt_inv (s : LvlState) (l : Nat) (h : LvlInv s) : LvlInv (acceptPkt s l) := by
  unfold LvlInv acceptPkt at *
  split <;> (first | omega | (simp only []; omega))

inductive Op where
  | install (l : Nat)
  | accept (l : Nat)

def apply (s : LvlState) : Op → LvlState
  | .install l => installKeys s l
  | .accept l  => acceptPkt s l

/-- **Encryption-level ordering (whole state machine)**: from a valid state, ANY
sequence of key installs and packet accepts keeps `maxAccepted <= currentLevel` —
ngtcp2 never processes a packet before its encryption keys are installed, for any
history.  By induction. -/
theorem seq_inv (ops : List Op) (s : LvlState) (h : LvlInv s) :
    LvlInv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o with
    | install l => exact installKeys_inv s l h
    | accept l  => exact acceptPkt_inv s l h

end NgtcpRV.ConnCryptoLevel
