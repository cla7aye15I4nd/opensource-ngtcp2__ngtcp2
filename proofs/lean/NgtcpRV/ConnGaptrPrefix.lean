import NgtcpRV.GaptrPush
/-!
gaptr contiguous-prefix property (gaptr.c `ngtcp2_gaptr_first_gap_offset`).

`ngtcp2_gaptr_first_gap_offset` returns the start of the first (lowest) gap — the
boundary up to which all offsets have been received contiguously.  For a gap set
whose gaps all start at or above `firstLo`, every offset below `firstLo` is NOT in
any gap, i.e. it is pushed.  So data `[0, first_gap_offset)` is fully received,
which is exactly what in-order stream delivery relies on.  We prove it on the
`GaptrPush` set-model.
-/
namespace NgtcpRV.ConnGaptrPrefix
open NgtcpRV.Gaptr NgtcpRV.RangeAlg

/-- **Contiguous prefix**: if every gap starts at or above `firstLo`, then any
offset below `firstLo` is not in any gap — it has been received. -/
theorem below_first_gap_received (gaps : List Range) (firstLo x : BitVec 64)
    (hsorted : ∀ g ∈ gaps, firstLo ≤ g.lo) (hx : x < firstLo) :
    ¬ unpushed x gaps := by
  unfold unpushed
  rintro ⟨g, hg, hmem⟩
  have hgl := hsorted g hg
  unfold mem at hmem
  obtain ⟨h1, _⟩ := hmem
  -- firstLo <= g.lo <= x  contradicts  x < firstLo
  exact absurd hx (by bv_omega)

end NgtcpRV.ConnGaptrPrefix
