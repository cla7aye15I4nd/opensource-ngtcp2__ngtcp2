/-!
ngtcp2_cpymem correctness (str.c) — the pervasive memory copy.

`ngtcp2_cpymem(dest, src, n)` copies the first `n` bytes of `src` to `dest` and
returns `dest + n` (so chained copies advance correctly).  We model the copied
bytes and prove the copy is exact (`dest[i] = src[i]` for `i < n`) and writes
exactly `n` bytes.
-/
namespace NgtcpRV.ConnCpymem

/-- The bytes `ngtcp2_cpymem` writes: the first `n` bytes of `src`. -/
def cpymem (src : List Nat) (n : Nat) : List Nat := src.take n

/-- Exactly `n` bytes are written (when `src` has them). -/
theorem cpymem_length (src : List Nat) (n : Nat) (h : n ≤ src.length) :
    (cpymem src n).length = n := by
  unfold cpymem; rw [List.length_take]; omega

/-- The copy is exact: every destination byte equals the source byte. -/
theorem cpymem_exact (src : List Nat) (n i : Nat) (hi : i < n) (hn : n ≤ src.length) :
    (cpymem src n)[i]? = src[i]? := by
  unfold cpymem; rw [List.getElem?_take_of_lt hi]

end NgtcpRV.ConnCpymem
