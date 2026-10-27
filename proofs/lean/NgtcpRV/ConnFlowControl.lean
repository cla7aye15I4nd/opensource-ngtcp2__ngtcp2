/-!
ngtcp2_conn flow control & anti-amplification: the credit subtractions never
underflow, and sending within the computed allowance preserves the limits.

  conn_fc_credits        = min(tx.max_offset - tx.offset, conn.max_offset - offset)
  conn_enforce_flow_ctrl = min(len, conn_fc_credits)
  dcid_tx_left           = bytes_recv*3 - bytes_sent   (the 3x anti-amplification)

These are the invariants that stop a peer from making us buffer unbounded data
(flow control) and stop us amplifying traffic to an unvalidated path (3x limit).
Modelled over `BitVec 64` (uint64, exact C wraparound semantics).
-/
namespace NgtcpRV.ConnFC

def minB (a b : BitVec 64) : BitVec 64 := if a ≤ b then a else b

/-- `conn_fc_credits`: the smaller of the stream and connection credits. -/
def fcCredits (soff smax coff cmax : BitVec 64) : BitVec 64 :=
  minB (smax - soff) (cmax - coff)

/-- `conn_enforce_flow_control(len)`: `len` capped by the available credit. -/
def enforce (soff smax coff cmax len : BitVec 64) : BitVec 64 :=
  minB len (fcCredits soff smax coff cmax)

/-- **Flow-control safety**: with the maintained invariant `offset ≤ max_offset`
on both the stream and the connection, sending at most `enforce(...)` bytes keeps
BOTH offsets within their granted maxima — no `uint64` underflow in the credit
computation, and the `offset ≤ max_offset` invariant is preserved. -/
theorem enforce_preserves (soff smax coff cmax len : BitVec 64)
    (hs : soff ≤ smax) (hc : coff ≤ cmax) :
    soff + enforce soff smax coff cmax len ≤ smax ∧
    coff + enforce soff smax coff cmax len ≤ cmax := by
  unfold enforce fcCredits minB
  constructor <;> (split <;> split <;> bv_omega)

/-- **Anti-amplification safety** (`dcid_tx_left`): with the maintained invariant
`bytes_sent ≤ cap` where `cap = 3 * bytes_recv` (exactly the `assert(dcid->
bytes_recv * 3 >= dcid->bytes_sent)`), the allowance `cap - bytes_sent` does not
underflow, and sending at most that keeps `bytes_sent ≤ 3 * bytes_recv` — the
endpoint never sends more than 3x what it received from an unvalidated path. -/
theorem tx_left_preserves (cap sent extra : BitVec 64)
    (hinv : sent ≤ cap) (hbound : extra ≤ cap - sent) :
    sent + extra ≤ cap := by bv_omega

end NgtcpRV.ConnFC
