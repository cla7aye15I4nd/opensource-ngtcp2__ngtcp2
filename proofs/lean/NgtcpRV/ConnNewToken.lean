/-!
NEW_TOKEN length validation (pkt.c / conn.c, RFC 9000 §19.7).

A NEW_TOKEN frame carries a token that MUST be non-empty — a zero-length token is
a FRAME_ENCODING_ERROR.  A received token is stored in a buffer sized to the
advertised length; validating `1 <= tokenlen` and `tokenlen <= capacity` makes the
copy well-defined and in bounds.  We prove the gate establishes both.
-/
namespace NgtcpRV.ConnNewToken

/-- The NEW_TOKEN validation: token is non-empty and fits the receive buffer. -/
def validToken (tokenlen capacity : Nat) : Bool :=
  decide (1 ≤ tokenlen ∧ tokenlen ≤ capacity)

/-- **Non-empty and in bounds**: a validated NEW_TOKEN has a positive length that
fits the buffer, so the token copy is well-defined and never overflows. -/
theorem token_valid (tokenlen capacity : Nat) (h : validToken tokenlen capacity = true) :
    1 ≤ tokenlen ∧ tokenlen ≤ capacity := by
  unfold validToken at h; simpa using h

/-- Every byte index of the token copy is within the buffer. -/
theorem token_copy_in_bounds (tokenlen capacity i : Nat)
    (h : validToken tokenlen capacity = true) (hi : i < tokenlen) : i < capacity := by
  have := token_valid tokenlen capacity h; omega

end NgtcpRV.ConnNewToken
