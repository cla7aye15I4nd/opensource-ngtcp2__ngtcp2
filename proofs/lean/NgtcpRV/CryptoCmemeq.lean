/-!
Constant-time comparison correctness (str.c `ngtcp2_cmemeq`).

`ngtcp2_cmemeq` compares two buffers in constant time:
`for i: rv |= a[i] ^ b[i]; return rv == 0;`.  It examines ALL n bytes (no early
return on the first mismatch) — the timing-attack defence used for secrets such
as stateless-reset tokens.  The byte-XOR-OR accumulator is nonzero iff some byte
differs, so the result equals "all bytes equal"; we model that accumulator as the
disjunction of per-byte inequalities (faithful: `a[i]^b[i] != 0 ↔ a[i] != b[i]`)
and prove the comparison is correct — true iff the buffers are equal.  (The
constant-time property is structural: the model folds over the whole list.)
-/
namespace NgtcpRV.CryptoCmemeq

/-- The accumulated "a mismatch was seen", over every byte (no early exit). -/
def anyMismatch (a b : List (BitVec 8)) : Bool :=
  (List.zipWith (fun x y => x != y) a b).any (fun c => c)

/-- `ngtcp2_cmemeq`: equal iff no mismatch was accumulated. -/
def cmemeq (a b : List (BitVec 8)) : Bool := !anyMismatch a b

/-- **Constant-time compare is correct**: for equal-length buffers it returns true
iff the buffers are equal — the OR-accumulator reports equality exactly, while
(structurally) always scanning all n bytes. -/
theorem cmemeq_correct (a b : List (BitVec 8)) (h : a.length = b.length) :
    cmemeq a b = true ↔ a = b := by
  unfold cmemeq anyMismatch
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp
    | cons y ys => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.zipWith_cons_cons, List.any_cons, Bool.not_or, Bool.and_eq_true,
          ih ys h, List.cons.injEq]
      constructor
      · rintro ⟨hx, hxs⟩
        exact ⟨by simpa using hx, hxs⟩
      · rintro ⟨rfl, hxs⟩
        exact ⟨by simp, hxs⟩

end NgtcpRV.CryptoCmemeq
