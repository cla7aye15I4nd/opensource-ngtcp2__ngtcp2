/-!
Connection-ID length validation (pkt.c / cid.c).

A connection ID is at most `NGTCP2_MAX_CIDLEN = 20` bytes and is stored in a fixed
20-byte buffer (`ngtcp2_cid.data`).  When parsing a long header, the length octet
is validated (`cil < MIN_CIDLEN || cil > MAX_CIDLEN -> reject`) BEFORE the bytes
are copied via `ngtcp2_cid_init` (whose `assert(datalen <= MAX_CIDLEN)` relies on
that check).  We prove a validated CID length makes the copy fit in the 20-byte
buffer — no overflow when reading an attacker-supplied connection ID.
-/
namespace NgtcpRV.ConnCidLen

def MAX_CIDLEN : Nat := 20
def MIN_CIDLEN : Nat := 1

/-- The parser's CID-length check (long header). -/
def validCid (cil : Nat) : Bool := decide (MIN_CIDLEN ≤ cil ∧ cil ≤ MAX_CIDLEN)

/-- **CID copy is in bounds**: a CID length that passes validation lies in
`[1, 20]`, so copying `cil` bytes into the 20-byte `cid->data` buffer never
overflows (and satisfies `ngtcp2_cid_init`'s assertion). -/
theorem cid_copy_safe (cil : Nat) (h : validCid cil = true) :
    1 ≤ cil ∧ cil ≤ MAX_CIDLEN ∧ cil ≤ 20 := by
  unfold validCid MAX_CIDLEN MIN_CIDLEN at *
  simp only [decide_eq_true_eq] at h
  omega

/-- The read range `[0, cil)` of the copy stays inside the 20-byte buffer. -/
theorem cid_read_in_buffer (cil i : Nat) (h : validCid cil = true) (hi : i < cil) :
    i < 20 := by
  unfold validCid MAX_CIDLEN MIN_CIDLEN at h
  simp only [decide_eq_true_eq] at h
  omega

end NgtcpRV.ConnCidLen
