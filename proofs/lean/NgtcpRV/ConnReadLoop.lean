import NgtcpRV.ConnDispatchState
/-!
# conn.c read loop over a packet stream `ngtcp2_conn_read_pkt` (lib/ngtcp2_conn.c)

Lifting `ConnDispatchState` (one packet's frame dispatch) to the connection's whole
received-packet stream: `ngtcp2_conn_read_pkt` is called repeatedly, each call recording the
packet number and dispatching the packet's frames.  We model the connection as the
flow-control/lifecycle state plus the largest received packet number, and prove that over
ANY sequence of received packets the flow-control invariant is preserved for the entire
connection lifetime and the largest-received packet number is monotone non-decreasing (the
acktr's tracking).
-/
namespace NgtcpRV.ConnReadLoop

open NgtcpRV.ConnDispatchState (CS Frame Inv recvPkt recvPkt_preserves)

/-- The connection: dispatch/flow-control state plus the largest received packet number. -/
structure Conn where
  cs : CS
  rxLargest : Int

/-- Process one received packet: record its number, dispatch its frames. -/
def processPkt (c : Conn) (pktNum : Int) (frames : List Frame) : Conn :=
  { cs := recvPkt c.cs frames, rxLargest := max c.rxLargest pktNum }

/-- The connection-level invariant (flow control holds). -/
def ConnInv (c : Conn) : Prop := Inv c.cs

/-- One packet preserves the connection invariant. -/
theorem processPkt_preserves (c : Conn) (pktNum : Int) (frames : List Frame) (h : ConnInv c) :
    ConnInv (processPkt c pktNum frames) := by
  unfold ConnInv processPkt at *; dsimp only
  exact recvPkt_preserves c.cs frames h

/-- One packet never lowers the largest received packet number. -/
theorem processPkt_rxLargest_mono (c : Conn) (pktNum : Int) (frames : List Frame) :
    c.rxLargest ≤ (processPkt c pktNum frames).rxLargest := by
  unfold processPkt; dsimp only; omega

/-- Replay the whole received-packet stream. -/
def runConn (c0 : Conn) (pkts : List (Int × List Frame)) : Conn :=
  pkts.foldl (fun c p => processPkt c p.1 p.2) c0

/-- **Connection-lifetime flow-control safety**: the invariant holds after any sequence of
received packets. -/
theorem runConn_preserves (c0 : Conn) (pkts : List (Int × List Frame)) (h : ConnInv c0) :
    ConnInv (runConn c0 pkts) := by
  unfold runConn
  induction pkts generalizing c0 with
  | nil => simpa using h
  | cons p pkts ih =>
    simp only [List.foldl_cons]
    exact ih _ (processPkt_preserves c0 p.1 p.2 h)

/-- **Largest-received monotonicity** over the connection lifetime. -/
theorem runConn_rxLargest_mono (c0 : Conn) (pkts : List (Int × List Frame)) :
    c0.rxLargest ≤ (runConn c0 pkts).rxLargest := by
  unfold runConn
  induction pkts generalizing c0 with
  | nil => simp
  | cons p pkts ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (processPkt_rxLargest_mono c0 p.1 p.2) (ih _)

end NgtcpRV.ConnReadLoop
