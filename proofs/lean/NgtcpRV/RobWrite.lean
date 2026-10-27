/-!
ngtcp2_rob rob_write_data: the chunk-buffer memcpy is in bounds.

rob buffers out-of-order stream data in fixed-size `chunk` buffers, each covering
an aligned range `r = [chunk_offset, chunk_offset + chunk)` with
`chunk_offset = (offset / chunk) * chunk`.  The write is
    memcpy(d + (offset - r.begin), data, n),  n = min(len, r.end - offset)
into the `chunk`-byte buffer `d`.  A wrong bound here is a heap overflow; we
prove the write stays within `[0, chunk)` for every offset and length.
-/
namespace NgtcpRV.Rob

/-- The chunk base `(offset / chunk) * chunk` contains `offset`:
`chunk_offset ≤ offset < chunk_offset + chunk`. -/
theorem chunk_contains (chunk offset : Nat) (hc : 0 < chunk) :
    (offset / chunk) * chunk ≤ offset ∧ offset < (offset / chunk) * chunk + chunk := by
  refine ⟨Nat.div_mul_le_self offset chunk, ?_⟩
  have h := Nat.div_add_mod offset chunk
  have h2 : chunk * (offset / chunk) = offset / chunk * chunk := Nat.mul_comm _ _
  have hm := Nat.mod_lt offset hc
  omega

/-- **Buffer safety of the memcpy** (abstract form): if the destination chunk
covers `offset` (`cbegin ≤ offset < cbegin + chunk`) then the write offset
`offset - cbegin` and the byte count `n = min(len, cend - offset)` together stay
within the `chunk`-byte buffer: `(offset - cbegin) + n ≤ chunk`. -/
theorem memcpy_in_bounds (chunk offset len cbegin : Nat)
    (hlo : cbegin ≤ offset) (hhi : offset < cbegin + chunk) :
    (offset - cbegin) < chunk ∧
    (offset - cbegin) + min len (cbegin + chunk - offset) ≤ chunk := by
  omega

/-- **rob_write_data memcpy safety** for the chunk the function actually uses:
`cbegin = (offset / chunk) * chunk`, `cend = cbegin + chunk`.  The copy
`d + (offset - cbegin) .. + n` never leaves the `chunk`-byte buffer, for every
`offset` and `len`.  (This is the exact `memcpy(d + (offset - r->begin), data,
ngtcp2_min(len, r->end - offset))` in lib/ngtcp2_rob.c.) -/
theorem write_data_safe (chunk offset len : Nat) (hc : 0 < chunk) :
    let cbegin := (offset / chunk) * chunk
    (offset - cbegin) < chunk ∧
    (offset - cbegin) + min len (cbegin + chunk - offset) ≤ chunk := by
  obtain ⟨hlo, hhi⟩ := chunk_contains chunk offset hc
  exact memcpy_in_bounds chunk offset len _ hlo hhi

end NgtcpRV.Rob
