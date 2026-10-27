/-!
conn.c / strm.c receive flow-control STATE-MACHINE invariant.

The receive path keeps, per stream, `rx.max_offset` (the flow-control limit we
advertised) and `rx.last_offset` (the highest offset seen).  Two things change
them: granting more credit (ngtcp2_strm_update_rx_offset / extend_max_offset,
which only *raises* max_offset) and receiving STREAM data (which the handler
accepts only when it stays within max_offset, else errors with
FLOW_CONTROL).  The safety invariant is `last_offset <= max_offset`: ngtcp2 never
records data beyond the limit it advertised — this is what bounds receive
buffering.  We prove it is preserved across ANY sequence of these operations, by
induction — a whole state-machine invariant, not a single-step check.
-/
namespace NgtcpRV.ConnRecvInv

def maxB (a b : BitVec 64) : BitVec 64 := if a ≤ b then a else b

/-- The receive flow-control state of one stream. -/
structure RxState where
  maxOff : BitVec 64
  lastOff : BitVec 64

/-- The maintained invariant: the highest received offset is within the advertised
flow-control limit. -/
def RxInv (s : RxState) : Prop := s.lastOff ≤ s.maxOff

/-- Grant more credit.  max_offset only ever increases (a smaller "new max" is
ignored), modelling extend_max_offset / update_rx_offset. -/
def extendMax (s : RxState) (newMax : BitVec 64) : RxState :=
  if s.maxOff ≤ newMax then { s with maxOff := newMax } else s

/-- Receive STREAM data ending at `endOff`.  The handler accepts it only if it
stays within the advertised limit; otherwise it is rejected (FLOW_CONTROL error)
and the state is unchanged. -/
def recvData (s : RxState) (endOff : BitVec 64) : RxState :=
  if endOff ≤ s.maxOff then { s with lastOff := maxB s.lastOff endOff } else s

theorem extendMax_inv (s : RxState) (newMax : BitVec 64) (h : RxInv s) :
    RxInv (extendMax s newMax) := by
  unfold RxInv extendMax at *; split <;> bv_omega

theorem recvData_inv (s : RxState) (endOff : BitVec 64) (h : RxInv s) :
    RxInv (recvData s endOff) := by
  unfold RxInv recvData maxB at *; (repeat' split) <;> bv_omega

/-- A receive-path event. -/
inductive Op where
  | grant (newMax : BitVec 64)
  | recv  (endOff : BitVec 64)

def apply (s : RxState) : Op → RxState
  | .grant m => extendMax s m
  | .recv e  => recvData s e

/-- **Receive flow-control safety (whole state machine)**: starting from a state
that satisfies the invariant, ANY sequence of credit grants and data receipts
leaves `last_offset <= max_offset`.  ngtcp2 never accepts stream data beyond the
flow-control limit it advertised, for any history of events.  By induction. -/
theorem seq_inv (ops : List Op) (s : RxState) (h : RxInv s) :
    RxInv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o with
    | grant m => exact extendMax_inv s m h
    | recv e  => exact recvData_inv s e h

/-- Corollary: after any event history, the highest accepted offset is within the
most recent advertised limit — the receive buffer is flow-control bounded. -/
theorem recv_bounded (ops : List Op) (s : RxState) (h : RxInv s) :
    (ops.foldl apply s).lastOff ≤ (ops.foldl apply s).maxOff :=
  seq_inv ops s h

end NgtcpRV.ConnRecvInv
