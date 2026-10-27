/-!
ngtcp2 range algebra (ngtcp2_range_{intersect,cut,len}) — the PARTITION invariant
that ngtcp2_gaptr / ngtcp2_rob / ngtcp2_acktr rely on when they split a gap `k`
by the overlapping piece `m = intersect(q,k)` and keep the left/right remainders.

The invariant: the three pieces l, m, r exactly tile k — same total length, no
offset lost, no offset double-counted, and they stay ordered and disjoint.
Proved semantically (not just machine-level read-safety) over `BitVec 64`,
matching the C `uint64_t` arithmetic exactly.
-/
namespace NgtcpRV.RangeAlg

structure Range where
  lo : BitVec 64
  hi : BitVec 64

/-- A range is well-formed when `begin ≤ end` (as every gap in the ksl is). -/
def wf (r : Range) : Prop := r.lo ≤ r.hi

/-- `ngtcp2_range_len`: `end - begin` (the true length for a well-formed range). -/
def len (r : Range) : BitVec 64 := r.hi - r.lo

def maxB (a b : BitVec 64) : BitVec 64 := if a ≤ b then b else a
def minB (a b : BitVec 64) : BitVec 64 := if a ≤ b then a else b

theorem right_le_maxB (a b : BitVec 64) : b ≤ maxB a b := by
  unfold maxB; split <;> bv_omega
theorem minB_le_right (a b : BitVec 64) : minB a b ≤ b := by
  unfold minB; split <;> bv_omega
theorem le_maxB_left (a b : BitVec 64) : a ≤ maxB a b := by
  unfold maxB; split <;> bv_omega
theorem minB_le_left (a b : BitVec 64) : minB a b ≤ a := by
  unfold minB; split <;> bv_omega

/-- `ngtcp2_range_intersect`. -/
def intersect (a b : Range) : Range :=
  let lo := maxB a.lo b.lo
  let hi := minB a.hi b.hi
  if lo < hi then ⟨lo, hi⟩ else ⟨0, 0⟩

/-- `ngtcp2_range_cut` (assumes `b ⊆ a`): left `[a.begin, b.begin)`, right `[b.end, a.end)`. -/
def cut (a b : Range) : Range × Range := (⟨a.lo, b.lo⟩, ⟨b.hi, a.hi⟩)

/-- When the intersection of `q` and a well-formed `k` is non-empty, it is a
sub-range of `k` (`k.lo ≤ m.lo ≤ m.hi ≤ k.hi`). -/
theorem intersect_sub (q k : Range)
    (hne : (intersect q k).lo < (intersect q k).hi) :
    k.lo ≤ (intersect q k).lo ∧ (intersect q k).lo ≤ (intersect q k).hi
      ∧ (intersect q k).hi ≤ k.hi := by
  unfold intersect at hne ⊢
  by_cases hg : maxB q.lo k.lo < minB q.hi k.hi
  · simp only [hg, if_true]
    have hmid : maxB q.lo k.lo ≤ minB q.hi k.hi := by
      have := le_maxB_left q.lo k.lo; have := minB_le_right q.hi k.hi; bv_omega
    exact ⟨right_le_maxB q.lo k.lo, hmid, minB_le_right q.hi k.hi⟩
  · simp only [hg, if_false] at hne
    exact absurd hne (by bv_omega)

/-- **PARTITION**: with `m = intersect(q,k)` non-empty and `(l,r) = cut(k,m)`,
the three pieces tile `k` exactly: `len l + len m + len r = len k`, and they are
well-formed and ordered (`k.lo ≤ l.hi = m.lo ≤ m.hi = r.lo ≤ k.hi`).  No offset
is lost or double-counted when the gap is split. -/
theorem cut_partition (q k : Range)
    (hne : (intersect q k).lo < (intersect q k).hi) :
    let m := intersect q k
    let l := (cut k m).1
    let r := (cut k m).2
    wf l ∧ wf r ∧ len l + len m + len r = len k
      ∧ l.hi = m.lo ∧ m.hi = r.lo := by
  intro m l r
  obtain ⟨h1, h2, h3⟩ := intersect_sub q k hne
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · show (cut k m).1.lo ≤ (cut k m).1.hi; simp only [cut]; exact h1
  · show (cut k m).2.lo ≤ (cut k m).2.hi; simp only [cut]; exact h3
  · show len l + len m + len r = len k
    simp only [l, r, cut, len]
    bv_omega

end NgtcpRV.RangeAlg
