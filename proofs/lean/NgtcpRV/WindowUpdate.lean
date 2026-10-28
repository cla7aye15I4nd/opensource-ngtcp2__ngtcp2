/-!
# conn.c flow-control window-update trigger

`conn_should_send_max_data` / `conn_should_send_max_stream_data`
(lib/ngtcp2_conn.c:3274) decide when to advertise more flow-control credit:

```c
  uint64_t inc = rx.unsent_max_offset - rx.max_offset;
  return rx.window < 4 * inc;
```
i.e. a MAX_DATA / MAX_STREAM_DATA frame is sent once the newly consumable amount
`inc` exceeds a quarter of the receive window.  `inc` is a `uint64_t` subtraction
that is sound because `unsent_max_offset >= max_offset` always holds (the unsent
limit never trails the sent one).

We prove the trigger fires exactly when more than a quarter of the window is
consumed, that it is monotone in `inc`, and that the `inc` subtraction never
underflows under the maintained invariant.
-/
namespace NgtcpRV.WindowUpdate

/-- `conn_should_send_max_data`: send an update when `window < 4 * inc`. -/
def shouldSend (window inc : Nat) : Bool := window < 4 * inc

/-- **Quarter-window trigger**: the update is sent exactly when the consumable amount
`inc` exceeds a quarter of the window. -/
theorem trigger_quarter (window inc : Nat) :
    shouldSend window inc = true ↔ window / 4 < inc := by
  unfold shouldSend
  rw [decide_eq_true_eq, Nat.div_lt_iff_lt_mul (by decide), Nat.mul_comm]

/-- The trigger is monotone in `inc`: once enough is consumed to send, consuming more
still sends. -/
theorem shouldSend_monotone (window : Nat) {i1 i2 : Nat} (h : i1 ≤ i2)
    (ht : shouldSend window i1 = true) : shouldSend window i2 = true := by
  unfold shouldSend at *; rw [decide_eq_true_eq] at *; omega

/-- A full (or empty) window with no consumption does not trigger an update. -/
theorem no_trigger_when_zero (window : Nat) : shouldSend window 0 = false := by
  unfold shouldSend; simp

/-- **inc underflow safety**: under the invariant `max_offset ≤ unsent_max_offset`, the
`uint64_t` subtraction `unsent - max` computes the true consumable amount without
wrapping. -/
theorem inc_no_underflow (unsent max : BitVec 64) (h : max ≤ unsent) :
    (unsent - max).toNat = unsent.toNat - max.toNat := by bv_omega

end NgtcpRV.WindowUpdate
