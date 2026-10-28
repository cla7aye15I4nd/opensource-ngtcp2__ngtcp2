/-!
# conn.c path equality is a proper equivalence `ngtcp2_path_eq` (lib/ngtcp2_path.c)

```c
  int ngtcp2_addr_eq(a, b) { return ngtcp2_sockaddr_eq(a->addr, b->addr); }
  int ngtcp2_path_eq(a, b) { return ngtcp2_addr_eq(&a->local, &b->local) &&
                                    ngtcp2_addr_eq(&a->remote, &b->remote); }
```

Path equality compares the local and remote addresses.  It is used pervasively to match
the current path (connection migration, the anti-amplification accounting, stateless
reset).  For that matching to be consistent it must be an equivalence relation and agree
with actual path identity.  Modelling addresses as values with decidable equality (as
`ngtcp2_sockaddr_eq` is byte equality), we prove `ngtcp2_path_eq` is reflexive, symmetric,
transitive, and holds exactly when the two paths are equal.
-/
namespace NgtcpRV.PathEq

/-- A path: a local and a remote address (addresses abstracted as values with `DecidableEq`,
matching the byte-equality of `ngtcp2_sockaddr_eq`). -/
structure Path (A : Type) where
  lcl : A
  rmt : A

/-- `ngtcp2_path_eq`: both addresses equal. -/
def pathEq {A : Type} [DecidableEq A] (p q : Path A) : Bool :=
  (p.lcl == q.lcl) && (p.rmt == q.rmt)

variable {A : Type} [DecidableEq A]

/-- `path_eq` holds exactly when the paths are equal. -/
theorem pathEq_iff (p q : Path A) : pathEq p q = true ↔ p = q := by
  unfold pathEq
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hl, hr⟩; cases p; cases q; simp_all
  · intro h; subst h; exact ⟨rfl, rfl⟩

/-- **Reflexive**. -/
theorem pathEq_refl (p : Path A) : pathEq p p = true := by rw [pathEq_iff]

/-- **Symmetric**. -/
theorem pathEq_symm (p q : Path A) (h : pathEq p q = true) : pathEq q p = true := by
  rw [pathEq_iff] at h ⊢; exact h.symm

/-- **Transitive**. -/
theorem pathEq_trans (p q r : Path A) (h1 : pathEq p q = true) (h2 : pathEq q r = true) :
    pathEq p r = true := by
  rw [pathEq_iff] at h1 h2 ⊢; exact h1.trans h2

/-- A path never matches one with a different remote address (path change detected). -/
theorem pathEq_false_of_rmt_ne (p q : Path A) (h : p.rmt ≠ q.rmt) : pathEq p q = false := by
  unfold pathEq; simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; right; exact h

end NgtcpRV.PathEq
