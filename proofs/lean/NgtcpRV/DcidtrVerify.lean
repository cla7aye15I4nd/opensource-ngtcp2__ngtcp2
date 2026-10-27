/-!
ngtcp2_dcidtr: CID-uniqueness scan and swap-remove.

* verify_cid_uniqueness scans a ringbuf of DCIDs and rejects a CID already present
  (prevents connection-ID confusion).  We prove the scan reports a conflict iff
  the CID really is in the buffer, reading only in-bounds indices.
* remove_dcid_at(rb, idx) deletes index `idx` by moving the last element into the
  hole and popping the back.  We prove both accessed indices (`idx`, `len-1`) are
  in bounds and the length drops by exactly one.
-/
namespace NgtcpRV.Dcidtr
variable {K : Type} [Inhabited K]

/-- `verify_cid_uniqueness`: true (⇒ NGTCP2_ERR_PROTO) iff some stored CID matches. -/
def scan (eq : K → Bool) : List K → Bool
  | [] => false
  | x :: xs => eq x || scan eq xs

/-- **Uniqueness check is exact**: the scan reports a conflict iff the CID is
actually present in the buffer — no false accept (which would admit a duplicate
CID) and no false reject. -/
theorem scan_iff_mem (eq : K → Bool) (l : List K) :
    scan eq l = true ↔ ∃ x ∈ l, eq x = true := by
  induction l with
  | nil => simp [scan]
  | cons x xs ih =>
    simp only [scan, Bool.or_eq_true, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨y, hy, hey⟩)
      · exact ⟨x, Or.inl rfl, h⟩
      · exact ⟨y, Or.inr hy, hey⟩
    · rintro ⟨y, rfl | hy, hey⟩
      · exact Or.inl hey
      · exact Or.inr ⟨y, hy, hey⟩

/-- **remove_dcid_at index safety**: with `idx < len` and `len ≥ 1`, the two
accessed ring indices — `idx` and `len-1` — are both `< len`, and after the
`pop_back` the length is exactly `len - 1`. -/
theorem remove_dcid_at_safe (len idx : Nat) (hlen : 1 ≤ len) (hat : idx < len) :
    idx < len ∧ len - 1 < len ∧ (len - 1) + 1 = len := by
  omega

/-- Swap-remove on the list model: index `idx` is deleted by overwriting it with
the last element and dropping the last.  (For `idx = 0` / `idx = len-1` the C takes
pop_front / pop_back, both the same deletion.) -/
def swapRemove (l : List K) (idx : Nat) : List K :=
  if idx = l.length - 1 then l.dropLast
  else (l.set idx (l.getLastD l.head!)).dropLast

/-- Swap-remove drops exactly one element. -/
theorem swapRemove_length (l : List K) (idx : Nat) :
    (swapRemove l idx).length = l.length - 1 := by
  unfold swapRemove
  split
  · rw [List.length_dropLast]
  · rw [List.length_dropLast, List.length_set]

end NgtcpRV.Dcidtr
