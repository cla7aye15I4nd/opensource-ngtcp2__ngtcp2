/-!
Two more conn.c helpers.

* conn_required_num_new_connection_id computes how many new connection IDs to
  provide.  Its inner `min(MAX_POOL, limit+retired) - len` can wrap (unsigned),
  but the outer `min(lim, n)` clamps the result, so the number of new CIDs is
  always bounded by the pool size — no unbounded CID allocation even if the inner
  subtraction underflows.
* buflen_align rounds a length up to a multiple of 8 (`(x+7)&~7`).
-/
namespace NgtcpRV.ConnCid

def minB (a b : BitVec 64) : BitVec 64 := if a ≤ b then a else b

/-- **CID count is bounded** (no resource exhaustion): whatever the inner
computation `n` evaluates to — even if its `min(...) - len` underflowed and
wrapped — the returned `min(lim, n)` is at most `lim = MAX_POOL - num_in_flight`,
hence at most `MAX_POOL`.  The outer `min` is what makes this safe. -/
theorem required_cid_bounded (maxPool inFlight n : BitVec 64)
    (hassert : inFlight ≤ maxPool) :
    minB (maxPool - inFlight) n ≤ maxPool := by
  unfold minB; split <;> bv_omega

/-- The returned count also never exceeds `lim` itself (the in-flight headroom). -/
theorem required_cid_le_lim (maxPool inFlight n : BitVec 64) :
    minB (maxPool - inFlight) n ≤ maxPool - inFlight := by
  unfold minB; split <;> bv_omega

/-- `buflen_align`: round `x` up to the next multiple of 8, `(x + 7) & ~7`. -/
def align8 (x : Nat) : Nat := (x + 7) / 8 * 8

theorem align8_ge (x : Nat) : x ≤ align8 x := by unfold align8; omega
theorem align8_lt (x : Nat) : align8 x < x + 8 := by unfold align8; omega
theorem align8_mod (x : Nat) : align8 x % 8 = 0 := by unfold align8; omega
/-- If `x` is already a multiple of 8, rounding is a no-op. -/
theorem align8_idem (x : Nat) (h : x % 8 = 0) : align8 x = x := by unfold align8; omega

end NgtcpRV.ConnCid
