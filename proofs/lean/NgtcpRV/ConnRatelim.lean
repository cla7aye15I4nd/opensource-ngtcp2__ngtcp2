/-!
Rate-limiter token-bucket invariant (ratelim.c).

`ngtcp2_ratelim` caps outbound work with a token bucket: `ratelim_update` adds
`gps` tokens but never past `burst` (it either adds when `tokens < burst - gps`,
or saturates to `burst`), and `ngtcp2_ratelim_drain` removes `n` tokens only when
`tokens >= n`.  The invariant is `tokens <= burst`: the bucket never over-fills,
so the rate limiter cannot be tricked into allowing a burst larger than
configured.  Proved across ANY update/drain history, by induction.
-/
namespace NgtcpRV.ConnRatelim

/-- Token-bucket state. -/
structure RlState where
  tokens : Nat
  burst : Nat

/-- The invariant: the bucket never holds more than `burst` tokens. -/
def RlInv (s : RlState) : Prop := s.tokens ≤ s.burst

/-- `ratelim_update`: add `gps` tokens, saturating at `burst` (the exact
`if (gps < burst && tokens < burst - gps) tokens += gps; else tokens = burst`). -/
def update (s : RlState) (gps : Nat) : RlState :=
  if gps < s.burst ∧ s.tokens < s.burst - gps then { s with tokens := s.tokens + gps }
  else { s with tokens := s.burst }

/-- `ngtcp2_ratelim_drain`: remove `n` tokens if available, else leave unchanged. -/
def drain (s : RlState) (n : Nat) : RlState :=
  if s.tokens < n then s else { s with tokens := s.tokens - n }

theorem update_inv (s : RlState) (gps : Nat) (_h : RlInv s) : RlInv (update s gps) := by
  unfold RlInv update
  split
  · rename_i hc; show s.tokens + gps ≤ s.burst; omega
  · show s.burst ≤ s.burst; omega

theorem drain_inv (s : RlState) (n : Nat) (h : RlInv s) : RlInv (drain s n) := by
  unfold RlInv drain at *
  split
  · exact h
  · show s.tokens - n ≤ s.burst; omega

/-- A rate-limiter event. -/
inductive Op where
  | update (gps : Nat)
  | drain (n : Nat)

def apply (s : RlState) : Op → RlState
  | .update gps => update s gps
  | .drain n    => drain s n

/-- **Token-bucket safety (whole state machine)**: from a valid state, ANY
sequence of updates and drains keeps `tokens <= burst` — the rate limiter never
over-fills, so it always enforces the configured burst.  By induction. -/
theorem seq_inv (ops : List Op) (s : RlState) (h : RlInv s) :
    RlInv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o with
    | update gps => exact update_inv s gps h
    | drain n    => exact drain_inv s n h

end NgtcpRV.ConnRatelim
