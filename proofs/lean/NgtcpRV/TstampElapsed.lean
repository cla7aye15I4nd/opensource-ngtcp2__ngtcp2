/-!
# conn.c timer expiry: `ngtcp2_tstamp_elapsed` / `ngtcp2_tstamp_not_elapsed`

These two inline helpers (lib/ngtcp2_tstamp.h) drive every timer in ngtcp2 (idle
timeout, PTO, keep-alive, CID retirement, …).  They handle the `uint64_t` overflow
edge cases explicitly; `UINT64_MAX` is a sentinel "no timestamp":

```c
int ngtcp2_tstamp_elapsed(base, d, ts)  { return base != MAX && base < MAX - d && base + d <= ts; }
int ngtcp2_tstamp_not_elapsed(base, d, ts){ return base != MAX && (base >= MAX - d || base + d > ts); }
```

Modelled at the real width (`BitVec 64`) and proved: the `base + d` addition the
`elapsed` branch performs never overflows (the `base < MAX - d` guard guarantees
it); the documented relationship `not_elapsed = ¬elapsed` holds exactly when
`base ≠ MAX`; an expired timer stays expired as time advances (monotone in `ts`);
and a not-yet-elapsed timer was also not elapsed at any earlier time.
-/
namespace NgtcpRV.TstampElapsed

/-- `UINT64_MAX`, the invalid-timestamp sentinel. -/
def MAXU : BitVec 64 := -1

/-- `ngtcp2_tstamp_elapsed`: at least `d` has passed since `base` (as a Prop; the C
returns nonzero in exactly these conditions). -/
def Elapsed (base d ts : BitVec 64) : Prop :=
  base ≠ MAXU ∧ base < MAXU - d ∧ base + d ≤ ts

/-- `ngtcp2_tstamp_not_elapsed`: `d` has not yet passed since `base`. -/
def NotElapsed (base d ts : BitVec 64) : Prop :=
  base ≠ MAXU ∧ (MAXU - d ≤ base ∨ ts < base + d)

/-- **Overflow safety**: whenever `elapsed` reaches the `base + d <= ts` test, the
`base < MAX - d` guard ensures `base + d` has not wrapped around. -/
theorem elapsed_no_overflow (base d ts : BitVec 64) (h : Elapsed base d ts) :
    (base + d).toNat = base.toNat + d.toNat := by
  obtain ⟨_, hlt, _⟩ := h
  simp only [MAXU] at hlt; bv_omega

/-- **Documented relationship**: for a valid base (`≠ UINT64_MAX`),
`not_elapsed` is exactly the negation of `elapsed`. -/
theorem not_elapsed_iff_not_elapsed (base d ts : BitVec 64) (hb : base ≠ MAXU) :
    NotElapsed base d ts ↔ ¬ Elapsed base d ts := by
  unfold NotElapsed Elapsed
  constructor
  · rintro ⟨_, hor⟩ ⟨_, hlt, hle⟩
    rcases hor with h | h
    · exact absurd hlt (by simp only [MAXU] at *; bv_omega)
    · exact absurd hle (by simp only [MAXU] at *; bv_omega)
  · intro h
    refine ⟨hb, ?_⟩
    by_cases hlt : base < MAXU - d
    · right
      rcases Classical.em (ts < base + d) with h2 | h2
      · exact h2
      · exact absurd ⟨hb, hlt, by simp only [MAXU] at *; bv_omega⟩ h
    · left; simp only [MAXU] at *; bv_omega

/-- **Expired stays expired**: once a timer has elapsed, it remains elapsed as the
current time advances. -/
theorem elapsed_mono (base d ts ts' : BitVec 64)
    (h : Elapsed base d ts) (hts : ts ≤ ts') : Elapsed base d ts' := by
  obtain ⟨hne, hlt, hle⟩ := h
  exact ⟨hne, hlt, by bv_omega⟩

/-- **Not-yet-elapsed in the past**: if a timer has not elapsed at a later time, it
had not elapsed at any earlier time either. -/
theorem not_elapsed_antitone (base d ts ts' : BitVec 64)
    (h : NotElapsed base d ts') (hts : ts ≤ ts') : NotElapsed base d ts := by
  obtain ⟨hne, hor⟩ := h
  refine ⟨hne, ?_⟩
  rcases hor with h | h
  · exact Or.inl h
  · exact Or.inr (by bv_omega)

/-- An invalid base (`UINT64_MAX`) is never considered elapsed nor not-elapsed. -/
theorem maxu_not_elapsed (d ts : BitVec 64) : ¬ Elapsed MAXU d ts := by
  rintro ⟨hne, _, _⟩; exact hne rfl

end NgtcpRV.TstampElapsed
