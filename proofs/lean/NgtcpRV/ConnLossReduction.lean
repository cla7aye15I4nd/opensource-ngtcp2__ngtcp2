/-!
Loss-reduction factor (cc.c, RFC 9002 §7.3.1).

On a congestion event ngtcp2 multiplies the window by the loss-reduction factor
`1/2`, implemented as `cstat->cwnd >>= NGTCP2_LOSS_REDUCTION_FACTOR_BITS` with
`FACTOR_BITS = 1`.  We prove the right shift by 1 equals integer division by 2, so
the reduction is exactly halving, and the halved window is at most the original.
-/
namespace NgtcpRV.ConnLossReduction

def LOSS_REDUCTION_FACTOR_BITS : Nat := 1

/-- The shift-based reduction equals halving. -/
theorem reduction_is_halving (cwnd : Nat) : cwnd >>> LOSS_REDUCTION_FACTOR_BITS = cwnd / 2 := by
  unfold LOSS_REDUCTION_FACTOR_BITS; rw [Nat.shiftRight_eq_div_pow]

/-- The reduced window never exceeds the original. -/
theorem reduced_le (cwnd : Nat) : cwnd >>> LOSS_REDUCTION_FACTOR_BITS ≤ cwnd := by
  rw [reduction_is_halving]; omega

end NgtcpRV.ConnLossReduction
