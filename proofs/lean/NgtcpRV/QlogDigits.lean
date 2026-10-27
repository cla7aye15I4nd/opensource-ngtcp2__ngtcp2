/-!
Decimal-length bound for uint64 (qlog.c / str.c).

qlog reserves a fixed overhead per event (`"length":` + up to ~20 digits) and
`ngtcp2_encode_uint(p, n)` writes the decimal digits of `n`.  The buffer-space
check is sound only because a `uint64_t` has at most 20 decimal digits
(2^64 - 1 = 18446744073709551615).  We prove `numDigits n <= 20` for every
`n < 2^64`.
-/
namespace NgtcpRV.QlogDigits

/-- Number of decimal digits of `n`. -/
def numDigits (n : Nat) : Nat := if n < 10 then 1 else 1 + numDigits (n / 10)
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- If `n < 10^d` with `d >= 1`, then `n` has at most `d` decimal digits. -/
theorem numDigits_le (d : Nat) : ∀ n : Nat, 1 ≤ d → n < 10 ^ d → numDigits n ≤ d := by
  induction d with
  | zero => intro n h _; omega
  | succ d ih =>
    intro n _ hn
    unfold numDigits
    split
    · omega
    · rename_i hge
      have hpow : (10 : Nat) ^ (d + 1) = 10 ^ d * 10 := by rw [Nat.pow_succ]
      have hd10 : n / 10 < 10 ^ d := by omega
      rcases Nat.eq_zero_or_pos d with hd0 | hdpos
      · subst hd0; simp only [Nat.pow_zero] at hd10; omega
      · have := ih (n / 10) hdpos hd10; omega

/-- **uint64 decimal length is bounded**: every `uint64_t` fits in at most 20
decimal digits, so `ngtcp2_encode_uint` never writes more than the 20 bytes the
qlog overhead reserves. -/
theorem uint64_numDigits_le_20 (n : Nat) (h : n < 2 ^ 64) : numDigits n ≤ 20 := by
  have hb : (2 : Nat) ^ 64 ≤ 10 ^ 20 := by decide
  exact numDigits_le 20 n (by omega) (by omega)

end NgtcpRV.QlogDigits
