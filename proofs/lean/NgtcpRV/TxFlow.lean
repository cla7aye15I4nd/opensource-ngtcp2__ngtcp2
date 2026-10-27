/-!
# conn.c TX flow control: send offsets never exceed the peer-advertised limits

Fifth stateful conn.c subsystem.  Outgoing data is capped by `conn_fc_credits`
(lib/ngtcp2_conn.c:1717):

```c
static uint64_t conn_fc_credits(const ngtcp2_conn *conn, ngtcp2_strm *strm) {
  return ngtcp2_min(strm->tx.max_offset - strm->tx.offset,
                    conn->tx.max_offset - conn->tx.offset);
}
```
and `conn_enforce_fc_credits` returns `ngtcp2_min(len, fc_credits)`, so no send ever
exceeds the remaining per-stream or connection credit.  The peer raises these
limits only upward, by sending MAX_STREAM_DATA / MAX_DATA (applied when the new
value exceeds the current one).

We model sends and limit-raises and prove, over ANY sequence of operations, the
invariant `tx.offset <= tx.max_offset` at both levels: the endpoint never sends
past what the peer authorized (RFC 9000 §4), and the `uint64_t` subtractions in
`conn_fc_credits` never underflow.
-/
namespace NgtcpRV.TxFlow

structure St where
  strmOff : Nat    -- strm->tx.offset
  strmMax : Nat    -- strm->tx.max_offset  (peer-advertised per-stream limit)
  connOff : Nat    -- conn->tx.offset
  connMax : Nat    -- conn->tx.max_offset  (peer-advertised connection limit)

def InvStrm (s : St) : Prop := s.strmOff ≤ s.strmMax
def InvConn (s : St) : Prop := s.connOff ≤ s.connMax
def Inv (s : St) : Prop := InvStrm s ∧ InvConn s

/-- `conn_fc_credits`: remaining send credit = min of per-stream and connection. -/
def fcCredits (s : St) : Nat := min (s.strmMax - s.strmOff) (s.connMax - s.connOff)

/-- Bytes actually sent for a request of `want` = `min(want, fc_credits)`. -/
def sent (s : St) (want : Nat) : Nat := min want (fcCredits s)

inductive Op
  | send (want : Nat)          -- write up to `want` bytes, fc-capped
  | raiseStrmMax (v : Nat)     -- MAX_STREAM_DATA: raise strm limit (upward only)
  | raiseConnMax (v : Nat)     -- MAX_DATA: raise conn limit (upward only)

def apply (s : St) : Op → St
  | .send want =>
      { s with strmOff := s.strmOff + sent s want, connOff := s.connOff + sent s want }
  | .raiseStrmMax v => { s with strmMax := max s.strmMax v }
  | .raiseConnMax v => { s with connMax := max s.connMax v }

/-- Enforcement: a send never exceeds the available flow-control credit. -/
theorem sent_le_credits (s : St) (want : Nat) : sent s want ≤ fcCredits s :=
  Nat.min_le_right _ _

/-- Each operation preserves the two flow-control invariants. -/
theorem apply_preserves (s : St) (op : Op) (h : Inv s) : Inv (apply s op) := by
  obtain ⟨hs, hc⟩ := h
  unfold InvStrm at hs; unfold InvConn at hc
  cases op with
  | send want =>
      refine ⟨?_, ?_⟩
      · show s.strmOff + sent s want ≤ s.strmMax
        unfold sent fcCredits; omega
      · show s.connOff + sent s want ≤ s.connMax
        unfold sent fcCredits; omega
  | raiseStrmMax v =>
      refine ⟨?_, ?_⟩
      · show s.strmOff ≤ max s.strmMax v; omega
      · show s.connOff ≤ s.connMax; omega
  | raiseConnMax v =>
      refine ⟨?_, ?_⟩
      · show s.strmOff ≤ s.strmMax; omega
      · show s.connOff ≤ max s.connMax v; omega

def run (s0 : St) (ops : List Op) : St := ops.foldl apply s0

/-- **TX flow-control safety** over ANY sequence of sends and limit-raises: both
`tx.offset <= tx.max_offset` invariants always hold — the endpoint never sends
past the peer-authorized limits. -/
theorem run_inv (s0 : St) (ops : List Op) (h : Inv s0) : Inv (run s0 ops) := by
  unfold run
  induction ops generalizing s0 with
  | nil => simpa using h
  | cons op ops ih =>
    simp only [List.foldl_cons]
    exact ih (apply s0 op) (apply_preserves s0 op h)

/-- Limits move only upward: MAX_STREAM_DATA / MAX_DATA never lower a limit. -/
theorem raiseStrmMax_mono (s : St) (v : Nat) : s.strmMax ≤ (apply s (.raiseStrmMax v)).strmMax := by
  show s.strmMax ≤ max s.strmMax v; omega
theorem raiseConnMax_mono (s : St) (v : Nat) : s.connMax ≤ (apply s (.raiseConnMax v)).connMax := by
  show s.connMax ≤ max s.connMax v; omega

/-- `conn_fc_credits` is underflow-free: under the invariant, the `uint64_t`
subtraction `max_offset - offset` is the true remaining credit at each level. -/
theorem credits_no_underflow (s : St) (h : Inv s) :
    s.strmMax - s.strmOff + s.strmOff = s.strmMax ∧
    s.connMax - s.connOff + s.connOff = s.connMax := by
  obtain ⟨hs, hc⟩ := h; unfold InvStrm at hs; unfold InvConn at hc
  exact ⟨by omega, by omega⟩

end NgtcpRV.TxFlow
