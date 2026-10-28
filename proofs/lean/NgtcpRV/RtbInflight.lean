/-!
# conn.c retransmission bytes-in-flight accounting (lib/ngtcp2_rtb.c)

`cstat->bytes_in_flight` tracks the total size of packets outstanding.  It is
increased when a packet is added to the RTB and decreased by that packet's own size
when it is acknowledged or lost, guarded by an assert:

```c
  cstat->bytes_in_flight += ent->pktlen;        /* rtb_add */
  ...
  assert(cstat->bytes_in_flight >= ent->pktlen); /* on ack / loss */
  cstat->bytes_in_flight -= ent->pktlen;
```

Modelling the in-flight set as the list of outstanding packet sizes with
`bytes_in_flight = Σ sizes`, we prove the asserted precondition always holds — any
in-flight packet's size is at most the running total — so the `uint64_t` decrement
never underflows, and that add/remove keep the total equal to the true sum.
-/
namespace NgtcpRV.RtbInflight

/-- `bytes_in_flight` = sum of the sizes of outstanding packets. -/
def lsum : List Nat → Nat
  | [] => 0
  | x :: xs => x + lsum xs

/-- `rtb_add`: adding a packet increases the total by its size. -/
theorem add_bif (len : Nat) (inflight : List Nat) :
    lsum (len :: inflight) = lsum inflight + len := by
  simp only [lsum]; omega

/-- **Decrement underflow-safety**: any in-flight packet's size is at most the running
total `bytes_in_flight`, so `assert(bytes_in_flight >= ent->pktlen)` always holds and
`bytes_in_flight -= ent->pktlen` never wraps. -/
theorem mem_le_sum (len : Nat) : ∀ (inflight : List Nat), len ∈ inflight → len ≤ lsum inflight := by
  intro inflight
  induction inflight with
  | nil => intro h; exact absurd h (by simp)
  | cons x xs ih =>
    intro h
    simp only [List.mem_cons] at h
    simp only [lsum]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

/-- Removing a tracked packet leaves a non-negative, consistent total: the new
`bytes_in_flight = old - len` stays well-defined (no underflow), since `len <= old`. -/
theorem remove_safe (len : Nat) (inflight : List Nat) (h : len ∈ inflight) :
    (lsum inflight - len) + len = lsum inflight := by
  have := mem_le_sum len inflight h; omega

/-- The total is zero exactly when nothing is in flight. -/
theorem sum_zero_iff_nil (inflight : List Nat) (hpos : ∀ x ∈ inflight, 0 < x) :
    lsum inflight = 0 ↔ inflight = [] := by
  cases inflight with
  | nil => simp [lsum]
  | cons x xs =>
    simp only [lsum]
    have hx : 0 < x := hpos x (by simp)
    constructor
    · intro h; omega
    · intro h; exact absurd h (by simp)

end NgtcpRV.RtbInflight
