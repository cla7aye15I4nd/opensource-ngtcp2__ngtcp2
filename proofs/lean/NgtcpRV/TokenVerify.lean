/-!
# conn.c token verification and version-list membership

Tenth stateful/helper conn.c cluster.  Two acceptance checks on attacker-controlled
input:

* `verify_token` (lib/ngtcp2_conn.c:6440): a server accepts the token echoed in a
  client packet only if the length AND every byte match the token it issued:
  ```c
  if (tokenlen == hd->tokenlen && ngtcp2_cmemeq(token, hd->token, tokenlen)) return 0;
  return NGTCP2_ERR_PROTO;
  ```
  So a client cannot have an arbitrary token accepted — exact match is required.

* `vneg_available_versions_includes` (lib/ngtcp2_conn.c:6455): tests whether a
  version appears in the peer's advertised `available_versions` list (used for
  version-downgrade detection).  Correctness = membership.

Both are modelled and their decision procedures proved sound and complete.
-/
namespace NgtcpRV.TokenVerify

/-- `verify_token`: accept iff lengths are equal and the byte sequences match. -/
def verifyToken (expected received : List Nat) : Bool :=
  (expected.length == received.length) && (expected == received)

/-- **Token exactness**: the token is accepted iff it exactly equals the issued
token — a client cannot get a different token accepted. -/
theorem verifyToken_iff (expected received : List Nat) :
    verifyToken expected received = true ↔ expected = received := by
  unfold verifyToken
  constructor
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.2
  · intro h; subst h; simp

/-- A token differing from the issued one is rejected. -/
theorem verifyToken_ne (expected received : List Nat) (h : expected ≠ received) :
    verifyToken expected received = false := by
  rw [Bool.eq_false_iff, ne_eq, verifyToken_iff]; exact h

/-- `vneg_available_versions_includes`: membership of `v` in the advertised list. -/
def vnegIncludes (versions : List Nat) (v : Nat) : Bool := versions.contains v

/-- Membership test is correct: it reports `true` exactly when `v` is advertised. -/
theorem vnegIncludes_iff (versions : List Nat) (v : Nat) :
    vnegIncludes versions v = true ↔ v ∈ versions := by
  unfold vnegIncludes; simp

/-- An empty advertised list includes no version. -/
theorem vnegIncludes_empty (v : Nat) : vnegIncludes [] v = false := rfl

end NgtcpRV.TokenVerify
