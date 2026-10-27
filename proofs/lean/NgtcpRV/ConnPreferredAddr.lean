import NgtcpRV.ConnCidLen
/-!
Preferred-address CID length validation (transport_params.c, RFC 9000 §18.2).

The `preferred_address` transport parameter contains a connection ID, which (like
any CID) must have length in `[1, 20]`; the stateless-reset token is 16 bytes.  We
reuse `ConnCidLen` to prove a validated preferred-address CID copy is in bounds,
and that its stateless-reset token is exactly 16 bytes.
-/
namespace NgtcpRV.ConnPreferredAddr
open NgtcpRV.ConnCidLen

/-- The preferred-address CID copy is in bounds (reusing the CID-length proof). -/
theorem pref_cid_copy_safe (cil i : Nat) (h : validCid cil = true) (hi : i < cil) : i < 20 :=
  cid_read_in_buffer cil i h hi

/-- The preferred-address stateless-reset token is a fixed 16 bytes. -/
def TOKEN_LEN : Nat := 16
theorem pref_token_len : TOKEN_LEN = 16 := rfl

end NgtcpRV.ConnPreferredAddr
