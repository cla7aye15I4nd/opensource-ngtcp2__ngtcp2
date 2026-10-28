import NgtcpRV.ConnDispatchState
/-!
# conn.c read loop with packet dedup (lib/ngtcp2_conn.c)

`ngtcp2_conn_read_pkt` records each accepted packet number and, via the acktr/gaptr,
refuses to reprocess a packet it has already seen (the `ngtcp2_gaptr_is_pushed` guard).
Composing dedup with the frame dispatch, we model the read loop with a set of received
packet numbers and prove: a duplicate packet is a no-op (its frames are NOT reprocessed —
replay/reprocessing protection), an accepted packet records its number, and the
flow-control invariant is preserved across any packet stream.
-/
namespace NgtcpRV.ConnDedup

open NgtcpRV.ConnDispatchState (CS Frame Inv recvPkt recvPkt_preserves)

/-- The connection: dispatch state plus the set of already-received packet numbers. -/
structure Conn where
  cs : CS
  seen : List Int

/-- Already processed this packet number? (`ngtcp2_gaptr_is_pushed`). -/
def isDup (c : Conn) (pn : Int) : Bool := c.seen.contains pn

/-- Process a received packet: drop duplicates, else dispatch and record the number. -/
def processPkt (c : Conn) (pn : Int) (frames : List Frame) : Conn :=
  if isDup c pn then c
  else { cs := recvPkt c.cs frames, seen := pn :: c.seen }

/-- **Replay protection**: a duplicate packet is a no-op — its frames are not reprocessed. -/
theorem dup_noop (c : Conn) (pn : Int) (frames : List Frame) (h : isDup c pn = true) :
    processPkt c pn frames = c := by
  unfold processPkt; rw [if_pos h]

/-- An accepted (non-duplicate) packet records its number as seen. -/
theorem accepted_recorded (c : Conn) (pn : Int) (frames : List Frame) (h : isDup c pn = false) :
    isDup (processPkt c pn frames) pn = true := by
  unfold processPkt; rw [if_neg (by simp [h])]
  unfold isDup; simp [List.contains_cons]

def ConnInv (c : Conn) : Prop := Inv c.cs

/-- One packet preserves the flow-control invariant (duplicate: unchanged; accepted: via
`recvPkt_preserves`). -/
theorem processPkt_preserves (c : Conn) (pn : Int) (frames : List Frame) (h : ConnInv c) :
    ConnInv (processPkt c pn frames) := by
  unfold ConnInv processPkt
  by_cases hd : isDup c pn
  · rw [if_pos hd]; exact h
  · rw [if_neg hd]; exact recvPkt_preserves c.cs frames h

def runConn (c0 : Conn) (pkts : List (Int × List Frame)) : Conn :=
  pkts.foldl (fun c p => processPkt c p.1 p.2) c0

/-- **Connection-lifetime safety**: the invariant holds after any packet stream, dedup and all. -/
theorem runConn_preserves (c0 : Conn) (pkts : List (Int × List Frame)) (h : ConnInv c0) :
    ConnInv (runConn c0 pkts) := by
  unfold runConn
  induction pkts generalizing c0 with
  | nil => simpa using h
  | cons p pkts ih =>
    simp only [List.foldl_cons]
    exact ih _ (processPkt_preserves c0 p.1 p.2 h)

end NgtcpRV.ConnDedup
