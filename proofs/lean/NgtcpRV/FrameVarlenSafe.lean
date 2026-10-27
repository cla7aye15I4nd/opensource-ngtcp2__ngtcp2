/-!
# Variable-length frame fields: the `payloadlen - len < vi` bounds check is
# underflow-free and correct

Several QUIC frame decoders carry a variable-length trailing field whose length
`vi` is itself read from the wire as a varint (CONNECTION_CLOSE reason, CRYPTO
data, NEW_TOKEN token, DATAGRAM data).  Each validates the field with the same C
idiom, where `len` is the bytes already consumed (header + the length varint):

```c
    if (payloadlen < len) return NGTCP2_ERR_FRAME_ENCODING;   // (guard)
    ngtcp2_get_uvarint(&vi, p);
    if (payloadlen - len < vi) return NGTCP2_ERR_FRAME_ENCODING;   // (field check)
    ... field occupies [len, len+vi) ...
```

`payloadlen`, `len`, `vi` are all `size_t` (unsigned).  The subtraction
`payloadlen - len` is the subtle part: if it could underflow it would wrap to a
value near `2^64` and the field check would wrongly pass, admitting an
out-of-bounds field.  The *preceding* guard `if (payloadlen < len) return`
is exactly what forbids that.  We prove both halves:

  * `sub_no_underflow` (BitVec 64, the real `size_t`): with the guard
    `len ≤ payloadlen`, `payloadlen - len` computes the true remaining byte count
    — no wraparound.  This is why the guard is load-bearing.
  * `field_check_correct` / `field_in_bounds`: under the guard, the field check
    accepts iff the field `[len, len+vi)` fits in `[0, payloadlen)`.
-/
namespace NgtcpRV.FrameVarlenSafe

/-- **Non-underflow** of the `size_t` subtraction, at the real width (`BitVec 64`):
when the guard `len ≤ payloadlen` holds, `payloadlen - len` equals the true
remaining count `payloadlen - len` in ℕ — it does NOT wrap.  Were the guard
absent, `(payloadlen - len).toNat` would instead be `payloadlen - len + 2^64`. -/
theorem sub_no_underflow (payloadlen len : BitVec 64) (hg : len ≤ payloadlen) :
    (payloadlen - len).toNat = payloadlen.toNat - len.toNat := by
  bv_omega

/-- **Field check correctness** (in ℕ, valid because `sub_no_underflow` shows the
C subtraction matches ℕ subtraction under the guard): with `len ≤ payloadlen`,
the C reject condition `payloadlen - len < vi` holds iff the field would overrun,
i.e. iff `payloadlen < len + vi`. -/
theorem field_check_correct (payloadlen len vi : Nat) (hg : len ≤ payloadlen) :
    payloadlen - len < vi ↔ payloadlen < len + vi := by omega

/-- **Spatial safety**: when the guard holds and the field check does NOT fire
(`¬ payloadlen - len < vi`), the whole field `[len, len + vi)` lies within the
buffer `[0, payloadlen)` — the end `len + vi ≤ payloadlen`, and when the field is
nonempty its start `len < payloadlen`. -/
theorem field_in_bounds (payloadlen len vi : Nat)
    (hg : len ≤ payloadlen) (hok : ¬ payloadlen - len < vi) :
    len + vi ≤ payloadlen ∧ (1 ≤ vi → len < payloadlen) := by
  constructor
  · omega
  · intro _; omega

/-- The BitVec guard `len ≤ payloadlen` and the ℕ guard agree (bridging the two
statements above). -/
theorem guard_toNat (payloadlen len : BitVec 64) :
    (len ≤ payloadlen) ↔ (len.toNat ≤ payloadlen.toNat) := by
  rw [BitVec.le_def]

end NgtcpRV.FrameVarlenSafe
