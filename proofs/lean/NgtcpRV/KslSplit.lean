/-!
ngtcp2_ksl B-tree node rebalancing: the split memcpy/memmove index arithmetic
stays within the fixed `NGTCP2_KSL_MAX_NBLK`-slot node/key arrays.

A ksl block holds up to `MAX_NBLK = 2*DEGR = 32` nodes.  `ksl_split_blk` halves a
full block; `ksl_split_node` opens a slot at `i` by shifting the tail right.
Both move raw memory by computed offsets into fixed-size arrays — the classic
place a B-tree off-by-one becomes a heap overflow.  We prove every source and
destination range lies inside `[0, MAX_NBLK)`, and that the halves stay balanced
(`>= MIN_NBLK`, the two asserts in ksl_split_blk).
-/
namespace NgtcpRV.KslSplit

def DEGR : Nat := 16
def MAX_NBLK : Nat := 2 * DEGR   -- 32
def MIN_NBLK : Nat := DEGR        -- 16

/-- **ksl_split_blk safety**: for a block of `n ≤ MAX_NBLK` nodes, the right block
gets `n/2`, the left keeps `n - n/2`; the two counts partition `n` (nothing lost)
and the source copy range `[left, left + right) = [n - n/2, n)` lies in
`[0, MAX_NBLK)`.  When the block is full (`n = MAX_NBLK`, the only case the code
splits) both halves equal `MIN_NBLK`, so the two `assert(... >= MIN_NBLK)` hold. -/
theorem split_blk_safe (n : Nat) (hn : n ≤ MAX_NBLK) :
    let rn := n / 2
    let ln := n - n / 2
    ln + rn = n ∧
    ln + rn ≤ MAX_NBLK ∧
    (n = MAX_NBLK → ln = MIN_NBLK ∧ rn = MIN_NBLK) := by
  unfold MAX_NBLK MIN_NBLK DEGR at *
  refine ⟨by omega, by omega, ?_⟩
  intro h; omega

/-- **ksl_split_node memmove safety (nodes array)**: with room to grow
(`n < MAX_NBLK`) and the split position `i < n`, the destination of
`memmove(nodes+(i+2), nodes+(i+1), (n-(i+1)))` is `[i+2, n+1) ⊆ [0, MAX_NBLK)`,
and the source `[i+1, n) ⊆ [0, MAX_NBLK)`. -/
theorem split_node_nodes_safe (n i : Nat) (hn : n < MAX_NBLK) (hi : i < n) :
    i + 2 + (n - (i + 1)) ≤ MAX_NBLK ∧ i + 1 + (n - (i + 1)) ≤ MAX_NBLK := by
  unfold MAX_NBLK DEGR at *; omega

/-- **ksl_split_node memmove safety (keys array)**: the destination of
`memmove(keys+(i+1)*klen, keys+i*klen, (n-i))` is `[i+1, n+1) ⊆ [0, MAX_NBLK)`
and the source `[i, n) ⊆ [0, MAX_NBLK)`, in key-slot units. -/
theorem split_node_keys_safe (n i : Nat) (hn : n < MAX_NBLK) (hi : i < n) :
    i + 1 + (n - i) ≤ MAX_NBLK ∧ i + (n - i) ≤ MAX_NBLK := by
  unfold MAX_NBLK DEGR at *; omega

/-- After `ksl_split_node` does `++blk->n`, the count is still within capacity. -/
theorem split_node_count_safe (n : Nat) (hn : n < MAX_NBLK) : n + 1 ≤ MAX_NBLK := by
  unfold MAX_NBLK DEGR at *; omega

end NgtcpRV.KslSplit
