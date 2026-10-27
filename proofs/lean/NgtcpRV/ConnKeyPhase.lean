/-!
Key-phase bit toggle (conn.c, RFC 9001 §6).

Each key update flips the Key Phase bit of outgoing 1-RTT packets, so a receiver
detects a key update by observing the bit change.  Two consecutive updates return
to the original phase (the bit has period 2), and the phase of a packet selects
which key generation decrypts it.  We prove the toggle alternates.
-/
namespace NgtcpRV.ConnKeyPhase

/-- The key phase after a key update: the current bit flipped. -/
def nextKeyPhase (current : Bool) : Bool := !current

/-- A key update flips the phase. -/
theorem update_flips (b : Bool) : nextKeyPhase b = !b := rfl

/-- Two key updates return to the original phase (period 2). -/
theorem two_updates_identity (b : Bool) : nextKeyPhase (nextKeyPhase b) = b := by
  unfold nextKeyPhase; simp

/-- The two key phases are distinct (so a phase change is always observable). -/
theorem phases_distinct (b : Bool) : nextKeyPhase b ≠ b := by
  unfold nextKeyPhase; simp

end NgtcpRV.ConnKeyPhase
