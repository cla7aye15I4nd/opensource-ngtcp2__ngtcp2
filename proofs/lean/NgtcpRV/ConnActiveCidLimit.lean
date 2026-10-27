/-!
active_connection_id_limit validation (transport_params.c, RFC 9000 §18.2).

The transport parameter `active_connection_id_limit` MUST be at least 2; a smaller
value is a TRANSPORT_PARAMETER_ERROR.  This guarantees an endpoint can always keep
at least two connection IDs in play (one in use, one spare for migration), so
connection migration is never starved.  We prove the validation establishes the
`>= 2` lower bound.
-/
namespace NgtcpRV.ConnActiveCidLimit

/-- The validation: `active_connection_id_limit` must be at least 2. -/
def validLimit (n : Nat) : Bool := decide (2 ≤ n)

/-- **At least two CIDs**: a validated `active_connection_id_limit` is `>= 2`, so a
spare connection ID is always available for migration. -/
theorem limit_ge_two (n : Nat) (h : validLimit n = true) : 2 ≤ n := by
  unfold validLimit at h; simpa using h

/-- Therefore at least one spare CID (beyond the one in use) is always permitted. -/
theorem spare_available (n : Nat) (h : validLimit n = true) : 1 ≤ n - 1 := by
  have := limit_ge_two n h; omega

end NgtcpRV.ConnActiveCidLimit
