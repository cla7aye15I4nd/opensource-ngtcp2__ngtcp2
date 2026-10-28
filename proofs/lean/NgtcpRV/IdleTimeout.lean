/-!
# conn.c idle-timeout expiry (RFC 9000 §10.1)

`ngtcp2_conn_get_idle_expiry` (lib/ngtcp2_conn.c) computes when a connection idles
out.  The effective timeout is the smaller of the two endpoints' advertised
`max_idle_timeout` (0 = "no limit"), floored at `3 * PTO`, with an overflow-guarded
final addition:

```c
  idle_timeout = <min of lcl/rmt max_idle_timeout, with 0-handling>;
  if (idle_timeout == 0) return UINT64_MAX;
  trpto = 3 * ngtcp2_conn_compute_pto(...);
  idle_timeout = ngtcp2_max(idle_timeout, trpto);
  if (conn->idle_ts >= UINT64_MAX - idle_timeout) return UINT64_MAX;
  return conn->idle_ts + idle_timeout;
```

We prove the effective timeout is never below `3 * PTO` (so the connection is not
dropped while still legitimately retransmitting), that it is the min of the two
advertised values when both are set, and that the final `idle_ts + idle_timeout`
addition never overflows (guarded; at the real `BitVec 64` width).
-/
namespace NgtcpRV.IdleTimeout

/-- Effective-timeout clamp `ngtcp2_max(idle_timeout, 3*PTO)`. -/
def effectiveTimeout (idleTimeout trpto : Nat) : Nat := max idleTimeout trpto

/-- **≥ 3·PTO**: the idle timeout is at least three PTOs. -/
theorem idle_at_least_3pto (idleTimeout trpto : Nat) : trpto ≤ effectiveTimeout idleTimeout trpto := by
  unfold effectiveTimeout; omega

/-- The negotiated idle timeout when both endpoints set a nonzero value: the C
selects `lcl` iff `lcl < rmt`, i.e. the minimum of the two. -/
def negotiated (lcl rmt : Nat) : Nat := if lcl < rmt then lcl else rmt

/-- With both advertised timeouts nonzero, the negotiated value is their min — the
stricter of the two endpoints governs. -/
theorem negotiated_eq_min (lcl rmt : Nat) : negotiated lcl rmt = min lcl rmt := by
  unfold negotiated; split <;> omega

theorem negotiated_le_local (lcl rmt : Nat) : negotiated lcl rmt ≤ lcl := by
  unfold negotiated; split <;> omega
theorem negotiated_le_remote (lcl rmt : Nat) : negotiated lcl rmt ≤ rmt := by
  unfold negotiated; split <;> omega

/-- `UINT64_MAX`. -/
def MAXU : BitVec 64 := -1

/-- The guarded final expiry `idle_ts + idle_timeout`, returning the sentinel on
would-be overflow. -/
def idleExpiry (idleTs idleTimeout : BitVec 64) : BitVec 64 :=
  if MAXU - idleTimeout ≤ idleTs then MAXU else idleTs + idleTimeout

/-- **Overflow safety**: when the guard does not fire, the final addition
`idle_ts + idle_timeout` does not wrap around (real `size_t`/`BitVec 64` width). -/
theorem idle_expiry_no_overflow (idleTs idleTimeout : BitVec 64)
    (h : ¬ MAXU - idleTimeout ≤ idleTs) :
    (idleTs + idleTimeout).toNat = idleTs.toNat + idleTimeout.toNat := by
  simp only [MAXU] at h; bv_omega

/-- When the guard does not fire, the returned expiry is exactly the (non-wrapping)
sum; otherwise it is the sentinel. -/
theorem idle_expiry_value (idleTs idleTimeout : BitVec 64)
    (h : ¬ MAXU - idleTimeout ≤ idleTs) :
    idleExpiry idleTs idleTimeout = idleTs + idleTimeout := by
  unfold idleExpiry; rw [if_neg h]

end NgtcpRV.IdleTimeout
