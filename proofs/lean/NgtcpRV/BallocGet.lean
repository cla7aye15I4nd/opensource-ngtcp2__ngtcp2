/-!
ngtcp2_balloc_get: the bump-allocator advance never overruns the block.

    *pbuf = buf.last;
    buf.last += (n + 0xF) & ~0xF;        // round n up to a multiple of 16

Read naively this looks unsafe: the refill guard is `buf_left < n`, but the
advance is `round16(n) >= n`, so when `buf_left == n` (not < n, no refill) the
pointer seems to move `round16(n) - n` bytes past the end.  It is in fact safe
because `buf.last` and `buf.end` are kept 16-aligned (ngtcp2_balloc_init aligns
the block and requires `blklen % 16 == 0`; every advance is a multiple of 16; the
`assert((uintptr_t)buf.last & 0xF == 0)` restates it).  Then `left = end - last`
is a multiple of 16, so `left >= n` already implies `left >= round16(n)`.
-/
namespace NgtcpRV.Balloc

/-- `(x + 0xF) & ~0xF` — round `x` up to the next multiple of 16. -/
def round16 (x : Nat) : Nat := (x + 15) / 16 * 16

theorem round16_ge (n : Nat) : n ≤ round16 n := by unfold round16; omega
theorem round16_lt (n : Nat) : round16 n < n + 16 := by unfold round16; omega
theorem round16_mul16 (n : Nat) : round16 n % 16 = 0 := by unfold round16; omega

/-- The no-refill branch is safe *because of* 16-alignment: if `left` is a multiple
of 16 and `left >= n`, then the rounded advance fits, `round16 n <= left`. -/
theorem round16_le_of_aligned (n left : Nat) (hal : left % 16 = 0) (hge : n ≤ left) :
    round16 n ≤ left := by unfold round16; omega

/-- After a refill the block has `blklen` bytes (a multiple of 16) and `n <= blklen`,
so the advance fits: `round16 n <= blklen`. -/
theorem round16_le_blklen (n blklen : Nat) (hb : blklen % 16 = 0) (hn : n ≤ blklen) :
    round16 n ≤ blklen := by unfold round16; omega

/-- **balloc_get advance safety**: with the maintained invariant (`left` and
`blklen` multiples of 16, `n <= blklen`), the bump advance stays within the block
on both paths — the no-refill path (`left >= n`) and the refill path (fresh
`blklen` block). -/
theorem balloc_get_safe (n left blklen : Nat)
    (hal : left % 16 = 0) (hbl : blklen % 16 = 0) (hn : n ≤ blklen) :
    (n ≤ left → round16 n ≤ left) ∧ round16 n ≤ blklen :=
  ⟨fun hge => round16_le_of_aligned n left hal hge, round16_le_blklen n blklen hbl hn⟩

end NgtcpRV.Balloc
