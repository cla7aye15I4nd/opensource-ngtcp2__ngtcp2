/-!
Send-side flow-control STATE-MACHINE invariant (conn.c / strm.c) — the dual of
`ConnRecvInv`.

Per stream the tx side tracks `tx.max_offset` (the limit the PEER advertised via
MAX_STREAM_DATA) and `tx.offset` (how many bytes we have sent).  The peer raising
the limit only increases `tx.max_offset`; `conn_enforce_flow_control` caps every
send to the remaining credit `tx.max_offset - tx.offset`.  The invariant is
`tx.offset <= tx.max_offset`: ngtcp2 never sends past the peer's advertised flow
-control limit, for any grant/send history.  By induction.
-/
namespace NgtcpRV.ConnSendInv

def minB (a b : BitVec 64) : BitVec 64 := if a ≤ b then a else b

/-- Per-stream tx flow-control state. -/
structure TxState where
  maxOff : BitVec 64
  offset : BitVec 64

/-- Invariant: bytes sent are within the peer's advertised limit. -/
def TxInv (s : TxState) : Prop := s.offset ≤ s.maxOff

/-- Peer grants more credit (MAX_STREAM_DATA); the limit only rises. -/
def grant (s : TxState) (newMax : BitVec 64) : TxState :=
  if s.maxOff ≤ newMax then { s with maxOff := newMax } else s

/-- Send up to `want` bytes; `conn_enforce_flow_control` caps the amount actually
sent at the remaining credit `maxOff - offset`. -/
def send (s : TxState) (want : BitVec 64) : TxState :=
  { s with offset := s.offset + minB want (s.maxOff - s.offset) }

theorem grant_inv (s : TxState) (newMax : BitVec 64) (h : TxInv s) :
    TxInv (grant s newMax) := by
  unfold TxInv grant at *; split <;> bv_omega

theorem send_inv (s : TxState) (want : BitVec 64) (h : TxInv s) :
    TxInv (send s want) := by
  unfold TxInv send minB at *; split <;> bv_omega

/-- A tx-side event. -/
inductive Op where
  | grant (newMax : BitVec 64)
  | send  (want : BitVec 64)

def apply (s : TxState) : Op → TxState
  | .grant m => grant s m
  | .send w  => send s w

/-- **Send flow-control safety (whole state machine)**: from a state satisfying
the invariant, ANY sequence of credit grants and sends keeps
`tx.offset <= tx.max_offset` — ngtcp2 never sends past the peer's advertised
limit, for any history.  By induction. -/
theorem seq_inv (ops : List Op) (s : TxState) (h : TxInv s) :
    TxInv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o with
    | grant m => exact grant_inv s m h
    | send w  => exact send_inv s w h

end NgtcpRV.ConnSendInv
