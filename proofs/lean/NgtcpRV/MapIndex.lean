/-!
# ngtcp2_map: hash-bucket indices stay within the table

`ngtcp2_map` (lib/ngtcp2_map.c) is a Robin-Hood open-addressing hash map over a
power-of-two table (`tablelen = 1 << hashbits`).  The initial bucket is the top
`hashbits` bits of the hashed key, and probing wraps with a mask:

```c
  size_t map_index(map, key)  { ...; return (size_t)(key >> (64 - map->hashbits)); }
  size_t mask = ((size_t)1 << map->hashbits) - 1;
  idx = (idx + 1) & mask;
```

Every access `map->keys[idx] / data[idx] / psl[idx]` is therefore in bounds iff
`idx < tablelen`.  We prove both: the initial index `key >> (64 - hashbits)` is
`< 2^hashbits`, and the probe step `(idx + 1) & (2^hashbits - 1)` is `< 2^hashbits`.
-/
namespace NgtcpRV.MapIndex

/-- **Probe index in bounds**: masking by `tablelen - 1` keeps the bucket index below
`tablelen = 2^hashbits`. -/
theorem probe_idx_lt (idx hashbits : Nat) :
    (idx &&& (2 ^ hashbits - 1)) < 2 ^ hashbits := by
  have h1 : idx &&& (2 ^ hashbits - 1) ≤ 2 ^ hashbits - 1 := Nat.and_le_right
  have h2 : 1 ≤ 2 ^ hashbits := Nat.one_le_two_pow
  omega

/-- **Initial index in bounds**: the top `hashbits` bits of the 64-bit hash are a
value `< 2^hashbits = tablelen`. -/
theorem map_index_lt (key : BitVec 64) (hashbits : Nat) (h : hashbits ≤ 64) :
    (key >>> (64 - hashbits)).toNat < 2 ^ hashbits := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hk : key.toNat < 2 ^ 64 := key.isLt
  have hsplit : (2 : Nat) ^ 64 = 2 ^ (64 - hashbits) * 2 ^ hashbits := by
    rw [← Nat.pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ (64 - hashbits) := Nat.one_le_two_pow
  have hlt : key.toNat < 2 ^ hashbits * 2 ^ (64 - hashbits) := by
    rw [Nat.mul_comm, ← hsplit]; exact hk
  exact (Nat.div_lt_iff_lt_mul hpos).mpr hlt

/-- Consequently, with `tablelen = 2^hashbits`, both the initial and the probed
indices are valid array positions. -/
theorem index_in_table (key : BitVec 64) (hashbits : Nat) (h : hashbits ≤ 64) :
    (key >>> (64 - hashbits)).toNat < 2 ^ hashbits ∧
    ∀ idx, (idx &&& (2 ^ hashbits - 1)) < 2 ^ hashbits :=
  ⟨map_index_lt key hashbits h, fun idx => probe_idx_lt idx hashbits⟩

end NgtcpRV.MapIndex
