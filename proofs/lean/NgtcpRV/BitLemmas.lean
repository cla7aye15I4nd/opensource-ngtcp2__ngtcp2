/-!
# Kernel-checked bit-vector facts

Everything here is proven with ordinary tactics (`simp`, `omega`, case
analysis on bits) that produce proof terms checked by the Lean kernel.
In particular nothing here uses `bv_decide` or `native_decide`, whose
certificates are checked by compiled code rather than by the kernel.
-/

namespace NgtcpRV.Bits

variable {w : Nat}

/-- The low-`k`-bit mask `(1 <<< k) - 1` has value `2^k - 1`. -/
theorem toNat_lowMask (k : Nat) (hk : k < w) :
    ((1#w <<< k) - 1#w).toNat = 2 ^ k - 1 := by
  have h2 : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) hk
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat]
  have e1 : (1 % 2 ^ w : Nat) = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  rw [e1, Nat.one_shiftLeft, Nat.mod_eq_of_lt h2]
  have e2 : 2 ^ w - 1 + 2 ^ k = (2 ^ k - 1) + 2 ^ w := by omega
  rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Masking with `(1 <<< k) - 1` is reduction modulo `2^k`. -/
theorem toNat_and_lowMask (x : BitVec w) (k : Nat) (hk : k < w) :
    (x &&& ((1#w <<< k) - 1#w)).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, toNat_lowMask (w := w) k hk, Nat.and_two_pow_sub_one_eq_mod]

/-- Bitwise identity: `x` splits into its high part and its low part. -/
theorem and_not_or_and (x m : BitVec w) : (x &&& ~~~m) ||| (x &&& m) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not]
  cases x.getLsbD i <;> cases m.getLsbD i <;> simp_all

theorem and_not_and_and (x y m : BitVec w) : (x &&& ~~~m) &&& (y &&& m) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases m.getLsbD i <;> simp_all

/-- Clearing the low `k` bits subtracts the remainder modulo `2^k`. -/
theorem toNat_clearLow (x : BitVec w) (k : Nat) (hk : k < w) :
    (x &&& ~~~((1#w <<< k) - 1#w)).toNat = x.toNat - x.toNat % 2 ^ k := by
  have hsum := BitVec.add_eq_or_of_and_eq_zero _ _ (and_not_and_and x x ((1#w <<< k) - 1#w))
  rw [and_not_or_and] at hsum
  have h := congrArg BitVec.toNat hsum
  rw [BitVec.toNat_add, toNat_and_lowMask x k hk] at h
  have hle : (x &&& ~~~((1#w <<< k) - 1#w)).toNat ≤ x.toNat := by
    rw [BitVec.toNat_and]; exact Nat.and_le_left
  have hlt := x.isLt
  have hm : x.toNat % 2 ^ k ≤ x.toNat := Nat.mod_le _ _
  generalize (x &&& ~~~((1#w <<< k) - 1#w)).toNat = A at h hle ⊢
  have hsmall : A + x.toNat % 2 ^ k < 2 ^ w := by
    apply Nat.lt_of_not_le; intro hge
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h
    omega
  rw [Nat.mod_eq_of_lt hsmall] at h
  omega

/-- `pn < 2^k` means `pn` has no bits at or above `k`. -/
theorem and_lowMask_of_lt (pn : BitVec w) (k : Nat) (hk : k < w) (h : pn.toNat < 2 ^ k) :
    pn &&& ((1#w <<< k) - 1#w) = pn := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_lowMask pn k hk, Nat.mod_eq_of_lt h]

/-- The candidate of RFC 9000 A.3: `(x & ~mask) | pn` is `x - x % 2^k + pn`
    (modulo `2^64`) when `pn < 2^k`. -/
theorem toNat_cand (x pn : BitVec w) (k : Nat) (hk : k < w) (h : pn.toNat < 2 ^ k) :
    ((x &&& ~~~((1#w <<< k) - 1#w)) ||| pn).toNat =
      (x.toNat - x.toNat % 2 ^ k + pn.toNat) % 2 ^ w := by
  have hz : (x &&& ~~~((1#w <<< k) - 1#w)) &&& pn = 0#w := by
    rw [← and_lowMask_of_lt pn k hk h]; exact and_not_and_and _ _ _
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hz, BitVec.toNat_add, toNat_clearLow x k hk]

/-- Low-`k`-bit extraction of a sum `a + pn` with `a` a multiple of `2^k`. -/
theorem toNat_and_lowMask_mod (x : BitVec 64) (k : Nat) (hk : k < 64) :
    (x &&& ((1#64 <<< k) - 1#64)) = BitVec.ofNat 64 (x.toNat % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_lowMask x k hk, BitVec.toNat_ofNat]
  have : x.toNat % 2 ^ k < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.mod_eq_of_lt this]

end NgtcpRV.Bits

namespace NgtcpRV.Bits

/-- clang's branch-free lowering of
    `if (cand > expected + hwin && cand >= win) cand - win else cand`. -/
theorem branchless_sub (c e H W : BitVec 64) :
    c - ((BitVec.setWidth 64 (BitVec.ofBool ((H + e).ult c)) ^^^ 1#64 |||
            BitVec.setWidth 64 (BitVec.ofBool (c.ult W))) + 18446744073709551615#64 &&& W) =
      if e + H < c ∧ W ≤ c then c - W else c := by
  have hcomm : H + e = e + H := BitVec.add_comm _ _
  have hones : ∀ x : BitVec 64, 18446744073709551615#64 &&& x = x := by
    intro x
    have : (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 := by decide
    rw [this, BitVec.allOnes_and]
  by_cases h1 : (H + e).ult c <;> by_cases h2 : c.ult W <;>
    simp only [h1, h2, BitVec.ofBool_true, BitVec.ofBool_false] <;>
    simp only [BitVec.ult_iff_lt, hcomm] at h1 h2
  · -- e + H < c, c < W: condition false
    have : ¬ W ≤ c := BitVec.not_le.mpr h2
    simp [this]
  · -- e + H < c, W ≤ c: condition true
    have hw : W ≤ c := BitVec.not_lt.mp h2
    simp [h1, hw, hones]
  · -- ¬ e + H < c, c < W
    simp [h1]
  · -- ¬ e + H < c, W ≤ c
    simp [h1]

end NgtcpRV.Bits

namespace NgtcpRV.Bits

theorem cases8 (x : BitVec 64) (h : x < 8#64) :
    x = 0#64 ∨ x = 1#64 ∨ x = 2#64 ∨ x = 3#64 ∨ x = 4#64 ∨ x = 5#64 ∨ x = 6#64 ∨ x = 7#64 := by
  rw [BitVec.lt_def] at h
  have : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3 ∨ x.toNat = 4 ∨
      x.toNat = 5 ∨ x.toNat = 6 ∨ x.toNat = 7 := by simp at h; omega
  rcases this with h|h|h|h|h|h|h|h <;> simp [BitVec.toNat_eq, h]

theorem cases1to4 (x : BitVec 64) (h1 : 1#64 ≤ x) (h4 : x ≤ 4#64) :
    x = 1#64 ∨ x = 2#64 ∨ x = 3#64 ∨ x = 4#64 := by
  rw [BitVec.le_def] at h1 h4
  have : x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3 ∨ x.toNat = 4 := by simp at h1 h4; omega
  rcases this with h|h|h|h <;> simp [BitVec.toNat_eq, h]

/-- A 4-byte-aligned return address survives `jalr`'s clearing of bit 0. -/
theorem align_clear0 (ra : BitVec 64) (h : ra &&& 3#64 = 0#64) :
    ra &&& 18446744073709551614#64 = ra := by
  have h3 : (3#64 : BitVec 64) = (1#64 <<< 2) - 1#64 := by decide
  have hm : (18446744073709551614#64 : BitVec 64) = ~~~((1#64 <<< 1) - 1#64) := by decide
  have h4 := congrArg BitVec.toNat h
  rw [h3, toNat_and_lowMask ra 2 (by decide)] at h4
  apply BitVec.eq_of_toNat_eq
  rw [hm, toNat_clearLow ra 1 (by decide)]
  simp at h4; omega

/-- ... and has bit 1 clear, so Sail's `jump_to` does not fault. -/
theorem align_bit1 (ra : BitVec 64) (h : ra &&& 3#64 = 0#64) : ra.extractLsb 1 1 = 0#1 := by
  have h3 : (3#64 : BitVec 64) = (1#64 <<< 2) - 1#64 := by decide
  have h4 := congrArg BitVec.toNat h
  rw [h3, toNat_and_lowMask ra 2 (by decide)] at h4
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb, Nat.shiftRight_eq_div_pow] at h4 ⊢
  omega

end NgtcpRV.Bits

namespace NgtcpRV.Bits

theorem ushr_eq_zero_iff (x : BitVec 64) (k : Nat) : x >>> k = 0#64 ↔ x.toNat < 2 ^ k := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  exact Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)

end NgtcpRV.Bits

namespace NgtcpRV.Bits

@[simp] theorem add_sub_cancel_left' (x y : BitVec 64) : x + y - x = y := by
  rw [BitVec.add_comm]; exact BitVec.add_sub_cancel y x

end NgtcpRV.Bits

namespace NgtcpRV.Bits

/-- An address outside `[d, d+8)` differs from every `d + k`, `k < 8`. -/
theorem ne_add_of_far (x d k : BitVec 64) (hk : k < 8#64) (hx : ¬ x - d < 8#64) : x ≠ d + k := by
  intro h; subst h; rw [add_sub_cancel_left'] at hx; exact hx hk

end NgtcpRV.Bits

namespace NgtcpRV.Bits

/-- Bits at or above `k` of a value below `2^k` are zero. -/
theorem getLsbD_of_lt_pow (x : BitVec 64) (k : Nat) (h : x.toNat < 2 ^ k) :
    ∀ i, k ≤ i → x.getLsbD i = false := by
  intro i hi
  rw [BitVec.getLsbD, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hi))]

end NgtcpRV.Bits

namespace NgtcpRV.Bits

/-- An address outside `[d, d+L)` differs from every `d + k`, `k < L`. -/
theorem ne_add_of_outside (x d k L : BitVec 64) (hk : k < L) (hx : ¬ x - d < L) : x ≠ d + k := by
  intro h; subst h; rw [add_sub_cancel_left'] at hx; exact hx hk

end NgtcpRV.Bits

namespace NgtcpRV.Bits

/-- `0 - [c]` is an all-ones mask when `c` holds and zero otherwise. -/
theorem mask_sel (c : Bool) (v : BitVec 64) :
    (0#64 - BitVec.setWidth 64 (BitVec.ofBool c)) &&& v = if c then v else 0#64 := by
  cases c
  · simp
  · have : (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 := by decide
    simp
    rw [this, BitVec.allOnes_and]

/-- Advancing an 8-aligned address by 8 keeps it 8-aligned. -/
theorem aligned_add8 (a : BitVec 64) (h : a.extractLsb 2 0 = 0#3) : (a + 8#64).extractLsb 2 0 = 0#3 := by
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb, BitVec.toNat_add] at h' ⊢
  omega

end NgtcpRV.Bits
