/-!
# conn.c stateless-reset detection: accepted only on an exact token match

Ninth stateful conn.c subsystem.  An incoming packet is treated as a Stateless
Reset only if `ngtcp2_dcid_verify_stateless_reset_token` (lib/ngtcp2_cid.c:134)
accepts it against a stored DCID:

```c
  return ngtcp2_path_eq(&dcid->ps.path, path) &&
         (dcid->flags & NGTCP2_DCID_FLAG_TOKEN_PRESENT) &&
         ngtcp2_cmemeq(dcid->token.data, token->data, sizeof(token->data))
       ? 0 : NGTCP2_ERR_INVALID_ARGUMENT;
```
`conn_on_stateless_reset` tries this against each stored DCID (current / bound /
retired).  RFC 9000 §10.3: a Stateless Reset is recognised only by a receiver that
holds the matching 128-bit token on the matching path — an attacker cannot forge
one without the secret token.  We prove the single-DCID unforgeability and the
aggregate scan.
-/
namespace NgtcpRV.StatelessReset

/-- A stored DCID's reset-token state: the 128-bit `token` and whether a token is
present (`NGTCP2_DCID_FLAG_TOKEN_PRESENT`). -/
structure Dcid where
  token : Nat
  tokenPresent : Bool

/-- `ngtcp2_dcid_verify_stateless_reset_token`: match iff the path matches
(`pathEq`), a token is present, and the token equals the incoming one. -/
def verify (d : Dcid) (pathEq : Bool) (incoming : Nat) : Bool :=
  pathEq && d.tokenPresent && (d.token == incoming)

/-- **Unforgeability**: a stateless reset is accepted only when the path matches, a
token is present, and the stored token equals the incoming token exactly. -/
theorem verify_sound (d : Dcid) (pathEq : Bool) (incoming : Nat)
    (h : verify d pathEq incoming = true) :
    pathEq = true ∧ d.tokenPresent = true ∧ d.token = incoming := by
  unfold verify at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- No token present ⇒ never accepted. -/
theorem verify_no_token (d : Dcid) (pathEq : Bool) (incoming : Nat)
    (h : d.tokenPresent = false) : verify d pathEq incoming = false := by
  unfold verify; simp [h]

/-- A mismatched token ⇒ never accepted (cannot forge with the wrong token). -/
theorem verify_wrong_token (d : Dcid) (pathEq : Bool) (incoming : Nat)
    (h : d.token ≠ incoming) : verify d pathEq incoming = false := by
  unfold verify; simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  right; exact h

/-- A wrong path ⇒ never accepted. -/
theorem verify_wrong_path (d : Dcid) (incoming : Nat) :
    verify d false incoming = false := by
  unfold verify; simp

/-- `conn_on_stateless_reset`: a packet is a stateless reset iff some stored DCID
(with its path-equality flag) verifies it. -/
def anyVerify (ds : List (Dcid × Bool)) (incoming : Nat) : Bool :=
  ds.any (fun p => verify p.1 p.2 incoming)

/-- **Aggregate unforgeability**: if the scan accepts, some stored DCID held a
present token equal to the incoming one on a matching path. -/
theorem anyVerify_sound (ds : List (Dcid × Bool)) (incoming : Nat)
    (h : anyVerify ds incoming = true) :
    ∃ p ∈ ds, p.2 = true ∧ p.1.tokenPresent = true ∧ p.1.token = incoming := by
  unfold anyVerify at h
  rw [List.any_eq_true] at h
  obtain ⟨p, hmem, hv⟩ := h
  obtain ⟨hpath, htp, htok⟩ := verify_sound p.1 p.2 incoming hv
  exact ⟨p, hmem, hpath, htp, htok⟩

/-- If no stored DCID holds the incoming token, no stateless reset is recognised. -/
theorem anyVerify_requires_token (ds : List (Dcid × Bool)) (incoming : Nat)
    (h : ∀ p ∈ ds, p.1.token ≠ incoming) : anyVerify ds incoming = false := by
  unfold anyVerify
  cases hb : ds.any (fun p => verify p.1 p.2 incoming) with
  | false => rfl
  | true =>
    rw [List.any_eq_true] at hb
    obtain ⟨p, hmem, hv⟩ := hb
    obtain ⟨_, _, htok⟩ := verify_sound p.1 p.2 incoming hv
    exact absurd htok (h p hmem)

end NgtcpRV.StatelessReset
