import NgtcpRV.RangeAlg
/-!
ngtcp2_gaptr_push, at the SET level: pushing the range `q` removes exactly the
offsets of `q` from the unpushed set, and touches nothing else.

A gaptr stores the still-unpushed offsets as a set of disjoint ranges (the ksl
gaps).  `ngtcp2_gaptr_push(offset, datalen)` walks the overlapping gaps and, for
each, replaces it by the parts not covered by `q = [offset, offset+datalen)`
(via ngtcp2_range_cut).  We model one gap's update and prove the exact set
equation; it rests on `RangeAlg` (every piece is a cut remainder).
-/
namespace NgtcpRV.Gaptr
open NgtcpRV.RangeAlg

/-- `x` lies in the half-open range `[lo, hi)` — ngtcp2's begin-inclusive,
end-exclusive convention. -/
def mem (x : BitVec 64) (r : Range) : Prop := r.lo ≤ x ∧ x < r.hi

/-- Subtract `q` from a single gap `k`: the unpushed remainder of `k`, exactly as
the loop body of `ngtcp2_gaptr_push` keeps (left and/or right of the overlap). -/
def removeGap (q k : Range) : List Range :=
  let m := intersect q k
  if m.lo < m.hi then
    (if k.lo < m.lo then [⟨k.lo, m.lo⟩] else []) ++
    (if m.hi < k.hi then [⟨m.hi, k.hi⟩] else [])
  else [k]

/-- The set of unpushed offsets represented by a list of gaps. -/
def unpushed (x : BitVec 64) (gaps : List Range) : Prop := ∃ g ∈ gaps, mem x g

/-- Key fact: for `x` already in gap `k`, being in `q` is the same as being in the
intersection `m = intersect(q,k)`. -/
theorem mem_inter_of_mem_k (q k : Range) (x : BitVec 64) (hk : mem x k) :
    mem x q ↔ mem x (intersect q k) := by
  obtain ⟨hkl, hkh⟩ := hk
  unfold intersect mem
  by_cases hg : maxB q.lo k.lo < minB q.hi k.hi
  · simp only [hg, if_true]
    unfold maxB minB at *
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨?_, ?_⟩ <;> (split <;> bv_omega)
    · rintro ⟨h1, h2⟩; revert h1 h2; split <;> split <;> intro h1 h2 <;> bv_omega
  · simp only [hg, if_false]
    unfold maxB minB at hg
    constructor
    · rintro ⟨h1, h2⟩; revert hg; split <;> split <;> intro hg <;> bv_omega
    · rintro ⟨h1, h2⟩; bv_omega

/-- **gaptr_push, single gap, set-level correctness**: after subtracting `q` from
gap `k`, the offsets still unpushed are exactly those that were in `k` and are
NOT in `q`.  Nothing outside `q` is lost; everything in `q` is removed. -/
theorem removeGap_correct (q k : Range) (x : BitVec 64) :
    unpushed x (removeGap q k) ↔ (mem x k ∧ ¬ mem x q) := by
  unfold removeGap unpushed
  by_cases hg : (intersect q k).lo < (intersect q k).hi
  · obtain ⟨h1, h2, h3⟩ := intersect_sub q k hg
    simp only [hg, if_true, List.mem_append]
    constructor
    · rintro ⟨g, hgin, hxlo, hxhi⟩
      -- g is the left or right remainder; either way x ∈ k and x ∉ m
      have hxk : mem x k := by
        rcases hgin with hl | hr
        · rcases (by split at hl <;> simp_all : k.lo < (intersect q k).lo ∧ g = ⟨k.lo, (intersect q k).lo⟩) with ⟨_, rfl⟩
          exact ⟨hxlo, by bv_omega⟩
        · rcases (by split at hr <;> simp_all : (intersect q k).hi < k.hi ∧ g = ⟨(intersect q k).hi, k.hi⟩) with ⟨_, rfl⟩
          exact ⟨by bv_omega, hxhi⟩
      refine ⟨hxk, ?_⟩
      rw [mem_inter_of_mem_k q k x hxk]
      rcases hgin with hl | hr
      · rcases (by split at hl <;> simp_all : k.lo < (intersect q k).lo ∧ g = ⟨k.lo, (intersect q k).lo⟩) with ⟨_, rfl⟩
        intro ⟨hm1, _⟩; bv_omega
      · rcases (by split at hr <;> simp_all : (intersect q k).hi < k.hi ∧ g = ⟨(intersect q k).hi, k.hi⟩) with ⟨_, rfl⟩
        intro ⟨_, hm2⟩; bv_omega
    · rintro ⟨hxk, hxq⟩
      rw [mem_inter_of_mem_k q k x hxk] at hxq
      simp only [mem] at hxk hxq ⊢
      -- x ∈ k and x ∉ m, so x ∈ [k.lo,m.lo) or x ∈ [m.hi,k.hi)
      by_cases hL : x < (intersect q k).lo
      · refine ⟨⟨k.lo, (intersect q k).lo⟩, ?_, ?_, ?_⟩
        · left; rw [if_pos (by bv_omega)]; simp
        · exact hxk.1
        · exact hL
      · refine ⟨⟨(intersect q k).hi, k.hi⟩, ?_, ?_, ?_⟩
        · right; rw [if_pos (by bv_omega)]; simp
        · bv_omega
        · exact hxk.2
  · simp only [hg, if_false, List.mem_singleton, exists_eq_left]
    -- m empty: k and q are disjoint, so x ∈ k ↔ (x ∈ k ∧ x ∉ q)
    constructor
    · intro hxk
      refine ⟨hxk, ?_⟩
      rw [mem_inter_of_mem_k q k x hxk]
      rintro ⟨a, b⟩; bv_omega
    · exact fun h => h.1

theorem unpushed_append (x : BitVec 64) (as bs : List Range) :
    unpushed x (as ++ bs) ↔ unpushed x as ∨ unpushed x bs := by
  unfold unpushed
  simp only [List.mem_append]
  constructor
  · rintro ⟨g, hg | hg, hm⟩
    · exact Or.inl ⟨g, hg, hm⟩
    · exact Or.inr ⟨g, hg, hm⟩
  · rintro (⟨g, hg, hm⟩ | ⟨g, hg, hm⟩)
    · exact ⟨g, Or.inl hg, hm⟩
    · exact ⟨g, Or.inr hg, hm⟩

theorem unpushed_cons (x : BitVec 64) (k : Range) (ks : List Range) :
    unpushed x (k :: ks) ↔ mem x k ∨ unpushed x ks := by
  unfold unpushed
  simp only [List.mem_cons]
  constructor
  · rintro ⟨g, rfl | hg, hm⟩
    · exact Or.inl hm
    · exact Or.inr ⟨g, hg, hm⟩
  · rintro (hm | ⟨g, hg, hm⟩)
    · exact ⟨k, Or.inl rfl, hm⟩
    · exact ⟨g, Or.inr hg, hm⟩

/-- Pushing `q` across the whole gap list. -/
def removeAll (q : Range) (gaps : List Range) : List Range := gaps.flatMap (removeGap q)

/-- **ngtcp2_gaptr_push, full set-level correctness**: after pushing `q`, the
offsets still unpushed are exactly those that were unpushed before and are not in
`q`.  Every offset of `q` becomes pushed; no other offset changes state.  Proved
by induction over the gap list, on top of `removeGap_correct`. -/
theorem removeAll_correct (q : Range) (gaps : List Range) (x : BitVec 64) :
    unpushed x (removeAll q gaps) ↔ (unpushed x gaps ∧ ¬ mem x q) := by
  induction gaps with
  | nil => simp [removeAll, unpushed]
  | cons k ks ih =>
    unfold removeAll
    simp only [List.flatMap_cons]
    rw [unpushed_append, ← removeAll, removeGap_correct, ih, unpushed_cons]
    constructor
    · rintro (⟨a, c⟩ | ⟨b, c⟩)
      · exact ⟨Or.inl a, c⟩
      · exact ⟨Or.inr b, c⟩
    · rintro ⟨a | b, c⟩
      · exact Or.inl ⟨a, c⟩
      · exact Or.inr ⟨b, c⟩

end NgtcpRV.Gaptr
