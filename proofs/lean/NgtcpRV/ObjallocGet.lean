import NgtcpRV.BallocGet
/-!
ngtcp2_objalloc: a typed object pool over ngtcp2_balloc.  `objalloc_X_get`
either reuses a freed object from the pool or calls
`ngtcp2_balloc_get(&balloc, &obj, sizeof(TYPE))`.  `objalloc_X_init` sizes the
balloc block as `round16(sizeof(TYPE)) * nmemb`.  We prove this sizing makes the
`balloc_get(sizeof(TYPE))` call satisfy balloc's preconditions — the block is a
multiple of 16 and the object fits — so the fixed-size allocation is memory-safe
(composing with `balloc_get_safe`).
-/
namespace NgtcpRV.Objalloc
open NgtcpRV.Balloc

/-- `ngtcp2_objalloc_X_init` sets `blklen = ((sizeof(TYPE)+0xF)&~0xF) * nmemb`. -/
def initBlklen (sz nmemb : Nat) : Nat := round16 sz * nmemb

/-- **objalloc sizing is sound**: with at least one object per block, the block
length is a multiple of 16 and the object request (`sizeof(TYPE)`) fits within it
— exactly balloc_get's two preconditions. -/
theorem init_blklen_ok (sz nmemb : Nat) (hn : 1 ≤ nmemb) :
    initBlklen sz nmemb % 16 = 0 ∧ sz ≤ initBlklen sz nmemb := by
  unfold initBlklen
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_mod, round16_mul16]; simp
  · calc sz ≤ round16 sz := round16_ge sz
    _ ≤ round16 sz * nmemb := Nat.le_mul_of_pos_right _ hn

/-- **objalloc_get fixed-size allocation is memory-safe**: for a block sized by
`objalloc_init`, the bump advance in the underlying `balloc_get(sizeof(TYPE))`
stays within the block on both paths.  Composition of `init_blklen_ok` with
`balloc_get_safe`. -/
theorem objalloc_get_safe (sz nmemb left : Nat) (hn : 1 ≤ nmemb)
    (hal : left % 16 = 0) :
    (sz ≤ left → round16 sz ≤ left) ∧ round16 sz ≤ initBlklen sz nmemb := by
  obtain ⟨hbl, hsz⟩ := init_blklen_ok sz nmemb hn
  exact balloc_get_safe sz left (initBlklen sz nmemb) hal hbl hsz

end NgtcpRV.Objalloc
