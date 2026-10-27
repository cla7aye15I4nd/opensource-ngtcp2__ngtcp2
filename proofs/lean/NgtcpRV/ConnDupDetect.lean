/-!
Duplicate-packet detection (acktr.c, RFC 9000 §12.3 / §21.1.3).

A received packet whose number has already been processed must be dropped (it is
a duplicate, possibly a replay).  ngtcp2 tracks received packet numbers (in the
acktr) and processes a packet only if its number is new.  We model the set of
received numbers and prove that re-receiving a number is detected as a duplicate,
while a genuinely new number is not — so each packet number is processed at most
once.
-/
namespace NgtcpRV.ConnDupDetect

/-- Whether packet number `pn` has already been received. -/
def isDuplicate (pn : Nat) (received : List Nat) : Bool := decide (pn ∈ received)

/-- A new packet number is not a duplicate. -/
theorem new_not_duplicate (pn : Nat) (received : List Nat) (h : pn ∉ received) :
    isDuplicate pn received = false := by
  unfold isDuplicate; simpa using h

/-- **Replay detected**: once a packet number has been received, re-receiving it is
detected as a duplicate (so it is processed at most once). -/
theorem replay_detected (pn : Nat) (received : List Nat) :
    isDuplicate pn (pn :: received) = true := by
  unfold isDuplicate; simp

end NgtcpRV.ConnDupDetect
