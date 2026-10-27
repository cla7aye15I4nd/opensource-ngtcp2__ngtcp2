import NgtcpRV.GaptrPush
/-!
ngtcp2_idtr (stream-ID tracker) is a thin layer over ngtcp2_gaptr: it stores the
unused internal IDs as gaps, `idtr_open(sid)` pushes the one-ID range `[q, q+1)`
(q = sid >> 2), and "open" means "pushed".  Its correctness therefore follows
directly from the gaptr set-model (`removeAll_correct`).
-/
namespace NgtcpRV.Idtr
open NgtcpRV.Gaptr NgtcpRV.RangeAlg

/-- The one-ID range `[q, q+1)` pushed by `ngtcp2_idtr_open`. -/
def singleton (q : BitVec 64) : Range := ⟨q, q + 1⟩

/-- An ID `q` is open iff it is no longer in the unused (gap) set. -/
def isOpen (q : BitVec 64) (gaps : List Range) : Prop := ¬ unpushed q gaps

/-- `ngtcp2_idtr_open q`: push `[q, q+1)` into the gap set. -/
def openId (q : BitVec 64) (gaps : List Range) : List Range :=
  removeAll (singleton q) gaps

/-- **idtr_open opens the ID**: after opening `q`, `q` is open — for every ID
`q` in range (`q < q+1`, which always holds for a stream ID `>> 2 < 2^60`). -/
theorem open_makes_open (q : BitVec 64) (gaps : List Range) (hq : q < q + 1) :
    isOpen q (openId q gaps) := by
  unfold isOpen openId
  rw [removeAll_correct]
  rintro ⟨_, hmem⟩
  apply hmem
  simp only [mem, singleton]
  exact ⟨by bv_omega, hq⟩

/-- **idtr_open touches no other ID**: opening `q` leaves the open/closed state of
every other ID `p` (one not equal to `q`, i.e. `p ∉ [q,q+1)`) unchanged. -/
theorem open_preserves_others (q p : BitVec 64) (gaps : List Range)
    (hp : ¬ mem p (singleton q)) :
    isOpen p (openId q gaps) ↔ isOpen p gaps := by
  unfold isOpen openId
  rw [removeAll_correct]
  constructor
  · intro h hu; exact h ⟨hu, hp⟩
  · intro h hc; exact h hc.1

/-- **in-use detection is exact**: `q` was already open (ngtcp2_idtr_open returns
STREAM_IN_USE) iff `q` is not in the unused set — i.e. `isOpen` is decidable by
exactly the `gaptr_is_pushed(q,1)` check the C code performs. -/
theorem is_open_iff_pushed (q : BitVec 64) (gaps : List Range) :
    isOpen q gaps ↔ ¬ unpushed q gaps := Iff.rfl

end NgtcpRV.Idtr
