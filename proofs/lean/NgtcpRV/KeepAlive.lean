/-!
# conn.c keep-alive timer (lib/ngtcp2_conn.c)

`conn_keep_alive_expiry` returns when the keep-alive timer fires, disabled
(`UINT64_MAX`) when cancelled, before handshake completion, when not enabled, or on
would-be overflow; otherwise `last_ts + timeout`:

```c
  if ((flags & KEEP_ALIVE_CANCELLED) || !(flags & HANDSHAKE_COMPLETED) ||
      !conn_keep_alive_enabled(conn) ||
      conn->keep_alive.last_ts >= UINT64_MAX - conn->keep_alive.timeout)
    return UINT64_MAX;
  return conn->keep_alive.last_ts + conn->keep_alive.timeout;
```

`conn_update_keep_alive_last_ts` rebases the timer and clears the CANCELLED flag.

We prove the final `last_ts + timeout` never overflows when the guard passes (real
`BitVec 64`), that any of cancelled / handshake-incomplete / disabled forces the
sentinel, and that rebasing re-arms the timer (clears CANCELLED).
-/
namespace NgtcpRV.KeepAlive

def MAXU : BitVec 64 := -1

structure KA where
  lastTs : BitVec 64
  timeout : BitVec 64
  cancelled : Bool
  handshakeDone : Bool
  enabled : Bool

/-- The would-overflow guard `last_ts >= UINT64_MAX - timeout`. -/
def overflowGuard (lastTs timeout : BitVec 64) : Bool := decide (MAXU - timeout ≤ lastTs)

/-- `conn_keep_alive_expiry`. -/
def expiry (k : KA) : BitVec 64 :=
  if k.cancelled || !k.handshakeDone || !k.enabled || overflowGuard k.lastTs k.timeout
  then MAXU else k.lastTs + k.timeout

/-- `conn_update_keep_alive_last_ts`: rebase and clear CANCELLED. -/
def updateLastTs (k : KA) (ts : BitVec 64) : KA := { k with lastTs := ts, cancelled := false }

/-- **Overflow safety**: when the guard passes (armed, handshake done, enabled, no
overflow), the timer expiry `last_ts + timeout` does not wrap. -/
theorem expiry_no_overflow (k : KA)
    (hc : k.cancelled = false) (hh : k.handshakeDone = true) (he : k.enabled = true)
    (ho : overflowGuard k.lastTs k.timeout = false) :
    (k.lastTs + k.timeout).toNat = k.lastTs.toNat + k.timeout.toNat := by
  unfold overflowGuard at ho
  simp only [MAXU, decide_eq_false_iff_not, BitVec.not_le] at ho
  bv_omega

/-- When the guard passes, the expiry is exactly the (non-wrapping) sum. -/
theorem expiry_value (k : KA)
    (hc : k.cancelled = false) (hh : k.handshakeDone = true) (he : k.enabled = true)
    (ho : overflowGuard k.lastTs k.timeout = false) :
    expiry k = k.lastTs + k.timeout := by
  simp [expiry, hc, hh, he, ho]

/-- A cancelled timer reports the sentinel (disabled). -/
theorem cancelled_disables (k : KA) (h : k.cancelled = true) : expiry k = MAXU := by
  simp [expiry, h]

/-- Before handshake completion the timer is disabled. -/
theorem handshake_incomplete_disables (k : KA) (h : k.handshakeDone = false) :
    expiry k = MAXU := by
  simp [expiry, h]

/-- A disabled keep-alive reports the sentinel. -/
theorem not_enabled_disables (k : KA) (h : k.enabled = false) : expiry k = MAXU := by
  simp [expiry, h]

/-- Rebasing the timer re-arms it: the CANCELLED flag is cleared. -/
theorem update_clears_cancelled (k : KA) (ts : BitVec 64) :
    (updateLastTs k ts).cancelled = false := rfl

end NgtcpRV.KeepAlive
