/-!
# conn.c PCG32 PRNG shift-amount safety `ngtcp2_pcg` (lib/ngtcp2_pcg.c)

```c
  static uint32_t pcg_rotr_32(uint32_t value, unsigned int rot) {
    return (value >> rot) | (value << ((32 - rot) & 31));
  }
  static uint32_t pcg_output_xsh_rr_64_32(uint64_t state) {
    return pcg_rotr_32((uint32_t)(((state >> 18) ^ state) >> 27), (unsigned int)(state >> 59));
  }
```

Rotations and shifts are only defined for shift amounts below the width.  Two facts make
this code well-defined: the rotate amount `state >> 59` is always `< 32` (it keeps the top
5 bits of a 64-bit word), and the counter-shift `(32 - rot) & 31` is always `<= 31 < 32`
(the `& 31` is what avoids the undefined `value << 32` when `rot == 0`).  We prove both at
the real bit widths.
-/
namespace NgtcpRV.Pcg

/-- The rotate amount used by the output function: top 5 bits of the 64-bit state. -/
theorem rot_amount_lt_32 (state : BitVec 64) : (state >>> 59).toNat < 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hk : state.toNat < 2 ^ 64 := state.isLt
  have hsplit : (2 : Nat) ^ 64 = 2 ^ 59 * 2 ^ 5 := by rw [← Nat.pow_add]
  have hpos : 0 < 2 ^ 59 := Nat.one_le_two_pow
  have hlt : state.toNat < 2 ^ 5 * 2 ^ 59 := by rw [Nat.mul_comm, ← hsplit]; exact hk
  have := (Nat.div_lt_iff_lt_mul hpos).mpr hlt
  simpa using this

/-- The counter-shift amount `(32 - rot) & 31` is always `<= 31`, so `value << (...)` is a
well-defined 32-bit shift — the `& 31` removes the `rot == 0` undefined-behaviour case. -/
theorem counter_shift_le_31 (rot : BitVec 32) : ((32#32 - rot) &&& 31#32).toNat ≤ 31 := by
  rw [BitVec.toNat_and]
  exact Nat.le_trans Nat.and_le_right (by decide)

/-- Consequently the counter-shift is a valid (`< 32`) shift distance. -/
theorem counter_shift_lt_32 (rot : BitVec 32) : ((32#32 - rot) &&& 31#32).toNat < 32 := by
  have := counter_shift_le_31 rot; omega

/-- The PCG LCG step is a total function of the state (`state := state * M + I` mod 2^64). -/
def step (state mult inc : BitVec 64) : BitVec 64 := state * mult + inc

/-- The step is deterministic: equal states step to equal states. -/
theorem step_deterministic (s1 s2 mult inc : BitVec 64) (h : s1 = s2) :
    step s1 mult inc = step s2 mult inc := by rw [h]

end NgtcpRV.Pcg
