/-!
ngtcp2_setmem correctness (str.c) — the padding zero-fill.

`ngtcp2_setmem(dest, c, n)` writes `n` copies of byte `c` and returns `dest + n`.
It is used to zero-fill PADDING (`ngtcp2_ppe_padding`), so every padding byte must
be the fill value and the written region is exactly `n` bytes.  We prove both.
-/
namespace NgtcpRV.ConnSetmem

/-- The bytes written by `ngtcp2_setmem(_, c, n)`. -/
def setmem (c n : Nat) : List Nat := List.replicate n c

/-- Exactly `n` bytes are written. -/
theorem setmem_length (c n : Nat) : (setmem c n).length = n := by
  unfold setmem; exact List.length_replicate ..

/-- Every written byte is the fill value `c` (so PADDING is all the pad byte). -/
theorem setmem_all (c n : Nat) : ∀ x ∈ setmem c n, x = c := by
  unfold setmem; intro x hx; exact List.eq_of_mem_replicate hx

/-- Padding writes all zero bytes. -/
theorem padding_all_zero (n : Nat) : ∀ x ∈ setmem 0 n, x = 0 := setmem_all 0 n

end NgtcpRV.ConnSetmem
