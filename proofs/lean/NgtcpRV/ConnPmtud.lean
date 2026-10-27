/-!
Path-MTU discovery binary search (pmtud.c, RFC 8899).

PMTU discovery probes packet sizes between a known-good lower bound `low` and an
upper bound `high` (the largest size worth trying), using a binary search: each
probe is `(low + high) / 2`.  A successful probe raises `low`; a failed one lowers
`high`.  We prove each probe lies within `[low, high]` and the search interval
strictly shrinks while `low < high`, so the discovery terminates and never probes
outside the valid range.
-/
namespace NgtcpRV.ConnPmtud

/-- The next probe size: midpoint of the current search interval. -/
def probe (low high : Nat) : Nat := (low + high) / 2

/-- **Probe in range**: the probe size is between the known-good lower bound and
the upper bound. -/
theorem probe_in_range (low high : Nat) (h : low ≤ high) :
    low ≤ probe low high ∧ probe low high ≤ high := by
  unfold probe; omega

/-- **Convergence**: while the interval is non-trivial (`low < high`), a successful
probe (raise `low` to just above the midpoint) or a failed probe (lower `high` to
the midpoint) strictly shrinks the interval. -/
theorem interval_shrinks (low high : Nat) (h : low < high) :
    high - (probe low high + 1) < high - low ∧ probe low high - low < high - low := by
  unfold probe; omega

end NgtcpRV.ConnPmtud
