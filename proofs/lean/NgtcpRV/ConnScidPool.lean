/-!
SCID pool size bound (conn.c, `NGTCP2_MAX_SCID_POOL_SIZE`).

An endpoint keeps at most `NGTCP2_MAX_SCID_POOL_SIZE = 8` source connection IDs in
its pool; `conn_required_num_new_connection_id` returns 0 once the pool is full
(`len >= NGTCP2_MAX_SCID_POOL_SIZE`).  We prove the full check bounds the pool and
that the number of new CIDs provided keeps the pool within the cap.
-/
namespace NgtcpRV.ConnScidPool

def MAX_SCID_POOL_SIZE : Nat := 8

/-- No new CIDs are provided once the pool is full. -/
def requiredNew (poolLen : Nat) : Nat :=
  if MAX_SCID_POOL_SIZE ≤ poolLen then 0 else MAX_SCID_POOL_SIZE - poolLen

/-- **Pool stays within the cap**: adding the required number of new CIDs keeps the
pool at or below `MAX_SCID_POOL_SIZE`. -/
theorem pool_within_cap (poolLen : Nat) (h : poolLen ≤ MAX_SCID_POOL_SIZE) :
    poolLen + requiredNew poolLen ≤ MAX_SCID_POOL_SIZE := by
  unfold requiredNew MAX_SCID_POOL_SIZE at *; split <;> omega

/-- A full pool requests no new CIDs. -/
theorem full_pool_no_new (poolLen : Nat) (h : MAX_SCID_POOL_SIZE ≤ poolLen) :
    requiredNew poolLen = 0 := by
  unfold requiredNew; rw [if_pos h]

end NgtcpRV.ConnScidPool
