/-!
Connection-ID equality (cid.c `ngtcp2_cid_eq`).

`ngtcp2_cid_eq` compares two connection IDs: equal iff they have the same length
and the same bytes.  This underlies DCID routing and the CID-uniqueness check.  We
model a CID as its byte list and prove `cidEq` decides structural equality — so CID
matching is exact (no false match on a prefix or different length).
-/
namespace NgtcpRV.ConnCidEq

/-- `ngtcp2_cid_eq`: same length and same bytes. -/
def cidEq (a b : List Nat) : Bool := decide (a.length = b.length) && decide (a = b)

/-- CID equality is exactly structural list equality. -/
theorem cidEq_iff (a b : List Nat) : cidEq a b = true ↔ a = b := by
  unfold cidEq
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · exact fun ⟨_, h⟩ => h
  · exact fun h => ⟨by rw [h], h⟩

/-- CIDs of different lengths are never equal (no cross-length confusion). -/
theorem different_length_ne (a b : List Nat) (h : a.length ≠ b.length) : cidEq a b = false := by
  unfold cidEq; simp [h]

end NgtcpRV.ConnCidEq
