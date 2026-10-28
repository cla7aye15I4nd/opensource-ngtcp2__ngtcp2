/-!
# conn.c received-range deduplication: `ngtcp2_gaptr`

`ngtcp2_gaptr` (lib/ngtcp2_gaptr.c) tracks which byte/number ranges have been
received, as the complement set of "gaps".  `ngtcp2_gaptr_push(off, len)` records a
range as received; `ngtcp2_gaptr_is_pushed(off, len)` returns nonzero iff
`[off, off+len)` no longer intersects any gap — i.e. the whole range has already
been received:

```c
  m = ngtcp2_range_intersect(&q, key);
  return ngtcp2_range_len(&m) == 0;     // empty intersection with the covering gap
```

This underpins dedup / replay protection throughout conn.c (e.g. the
`ngtcp2_gaptr_is_pushed(&conn->dcid.seqgap, fr->seq, 1)` guard that drops a
duplicate NEW_CONNECTION_ID, and CRYPTO/STREAM reordering).  We model the received
set directly (the complement of the gaps) and prove the dedup contract: once a
range is pushed it reads back as pushed, and `is_pushed` is monotone — so a
duplicate is always detected and never reprocessed.
-/
namespace NgtcpRV.GaptrDedup

/-- A received interval `[begin, end)`. -/
abbrev Interval := Nat × Nat

/-- `x` lies in `[iv.1, iv.2)`. -/
def inRange (iv : Interval) (x : Nat) : Prop := iv.1 ≤ x ∧ x < iv.2

/-- `x` has been received (lies in some pushed interval) — the complement of the
gap set that `gaptr` stores. -/
def seenBy (ivs : List Interval) (x : Nat) : Prop := ∃ iv ∈ ivs, inRange iv x

/-- `ngtcp2_gaptr_is_pushed`: every number in `[off, off+len)` has been received. -/
def isPushed (ivs : List Interval) (off len : Nat) : Prop :=
  ∀ x, off ≤ x → x < off + len → seenBy ivs x

/-- `ngtcp2_gaptr_push`: record `[off, off+len)` as received. -/
def push (ivs : List Interval) (off len : Nat) : List Interval := (off, off + len) :: ivs

/-- **Dedup contract**: immediately after pushing a range, `is_pushed` reports it as
pushed — so a subsequent duplicate of that exact range is detected. -/
theorem push_then_isPushed (ivs : List Interval) (off len : Nat) :
    isPushed (push ivs off len) off len := by
  intro x h1 h2
  exact ⟨(off, off + len), by simp [push], h1, h2⟩

/-- **Monotonicity**: pushing further ranges never un-marks an already-pushed range,
so once a packet number is seen it stays seen (no reprocessing window reopens). -/
theorem isPushed_monotone (ivs : List Interval) (off len o2 l2 : Nat)
    (h : isPushed ivs off len) : isPushed (push ivs o2 l2) off len := by
  intro x h1 h2
  obtain ⟨iv, hmem, hr⟩ := h x h1 h2
  exact ⟨iv, by simp [push, hmem], hr⟩

/-- Nothing is pushed in the initial empty state (a first, nonempty range is new). -/
theorem isPushed_empty_false (off len : Nat) (h : 1 ≤ len) : ¬ isPushed [] off len := by
  intro hp
  obtain ⟨iv, hmem, _⟩ := hp off (Nat.le_refl _) (by omega)
  exact absurd hmem (by simp)

/-- A duplicate of a just-pushed range is detected: pushing the same `(off,len)`
again finds it already present. -/
theorem duplicate_detected (ivs : List Interval) (off len : Nat) :
    isPushed (push ivs off len) off len := push_then_isPushed ivs off len

end NgtcpRV.GaptrDedup
