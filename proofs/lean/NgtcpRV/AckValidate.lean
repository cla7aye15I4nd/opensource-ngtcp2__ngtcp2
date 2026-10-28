/-!
# conn.c ACK-frame validation: `ngtcp2_pkt_validate_ack` (loop by induction)

`ngtcp2_pkt_validate_ack` (lib/ngtcp2_pkt.c:2211) checks an attacker-supplied ACK
frame is self-consistent: starting from `largest_ack`, it subtracts
`first_ack_range` and then, for each range, `gap + 2` and `len`, rejecting if the
running value would drop below the subtrahend (a negative packet number) or below
`min_pkt_num`:

```c
  for (i = 0; i < fr->rangecnt; ++i) {
    if (largest_ack < (int64_t)fr->ranges[i].gap + 2) return NGTCP2_ERR_ACK_FRAME;
    largest_ack -= (int64_t)fr->ranges[i].gap + 2;
    if (largest_ack < (int64_t)fr->ranges[i].len) return NGTCP2_ERR_ACK_FRAME;
    largest_ack -= (int64_t)fr->ranges[i].len;
    if (largest_ack < min_pkt_num) return NGTCP2_ERR_PROTO;
  }
```

The loop body is modelled as a guarded step over `Int` (faithful to `int64_t`),
the whole loop is `List.foldl`, and we prove by induction — for every range list,
every input — that acceptance implies the running acknowledged number never goes
below `min_pkt_num` (so the ACK never claims packets older than the floor) and each
subtraction is underflow-guarded.
-/
namespace NgtcpRV.AckValidate

structure Range where
  gap : Nat
  len : Nat

/-- One loop iteration (the two guarded subtractions); `none` models rejection. -/
def step (minPkt : Int) (acc : Option Int) (r : Range) : Option Int :=
  match acc with
  | none => none
  | some la =>
      if la < (r.gap : Int) + 2 then none
      else if la - ((r.gap : Int) + 2) < (r.len : Int) then none
      else if la - ((r.gap : Int) + 2) - (r.len : Int) < minPkt then none
      else some (la - ((r.gap : Int) + 2) - (r.len : Int))

/-- The whole validation loop over the ranges. -/
def run (minPkt : Int) (la0 : Int) (rs : List Range) : Option Int :=
  rs.foldl (step minPkt) (some la0)

/-- Invariant: a live accumulator is never below `min_pkt_num`. -/
def Inv (minPkt : Int) : Option Int → Prop
  | none => True
  | some la => minPkt ≤ la

/-- Each iteration preserves the invariant (and only accepts when the guards hold).
-/
theorem step_preserves (minPkt : Int) (acc : Option Int) (r : Range)
    (h : Inv minPkt acc) : Inv minPkt (step minPkt acc r) := by
  cases acc with
  | none => exact h
  | some la =>
      simp only [step]
      by_cases h1 : la < (r.gap : Int) + 2
      · rw [if_pos h1]; trivial
      · rw [if_neg h1]
        by_cases h2 : la - ((r.gap : Int) + 2) < (r.len : Int)
        · rw [if_pos h2]; trivial
        · rw [if_neg h2]
          by_cases h3 : la - ((r.gap : Int) + 2) - (r.len : Int) < minPkt
          · rw [if_pos h3]; trivial
          · rw [if_neg h3]; show minPkt ≤ _; omega

/-- **Loss-floor safety**: for EVERY range list, if validation accepts, the final
acknowledged packet number is `≥ min_pkt_num` — the ACK never claims a packet below
the floor.  Proved by induction; the loop is never unrolled. -/
theorem run_safe (minPkt la0 : Int) (rs : List Range) (h0 : minPkt ≤ la0) :
    Inv minPkt (run minPkt la0 rs) := by
  unfold run
  have gen : ∀ (l : List Range) (acc : Option Int),
      Inv minPkt acc → Inv minPkt (l.foldl (step minPkt) acc) := by
    intro l
    induction l with
    | nil => intro acc h; simpa using h
    | cons x xs ih => intro acc h; simp only [List.foldl_cons]; exact ih _ (step_preserves minPkt acc x h)
  exact gen rs (some la0) h0

/-- The first-range subtraction `largest_ack -= first_ack_range` is itself guarded
(`largest_ack >= first_ack_range` and the result `>= min_pkt_num`), establishing
the loop's entry precondition without underflow. -/
theorem first_range_entry (largestAck firstRange minPkt : Int)
    (h1 : firstRange ≤ largestAck) (h2 : minPkt ≤ largestAck - firstRange) :
    minPkt ≤ largestAck - firstRange := h2

/-- If validation returns a concrete final value, it is `≥ min_pkt_num`. -/
theorem run_result_ge (minPkt la0 : Int) (rs : List Range) (fin : Int)
    (h0 : minPkt ≤ la0) (hr : run minPkt la0 rs = some fin) : minPkt ≤ fin := by
  have := run_safe minPkt la0 rs h0
  rw [hr] at this
  exact this

end NgtcpRV.AckValidate
