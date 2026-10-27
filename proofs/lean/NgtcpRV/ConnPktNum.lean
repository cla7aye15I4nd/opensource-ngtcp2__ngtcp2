/-!
Packet-number-space STATE-MACHINE invariant (conn.c / rtb.c).

Each packet-number space tracks `tx.last_pkt_num` (the last number we assigned a
sent packet) and `rtb.largest_acked_tx_pkt_num` (the largest of our packets the
peer has acknowledged).  Sending assigns the next number (`last_pkt_num + 1`);
processing an ACK advances `largest_acked` toward the acknowledged number, but a
valid ACK can only acknowledge a packet we actually sent.  The invariant is
`largest_acked <= last_pkt_num`: ngtcp2 never treats an unsent packet number as
acknowledged (which would corrupt RTT / loss-recovery accounting).  Preserved
across ANY send/ack history, by induction.
-/
namespace NgtcpRV.ConnPktNum

def maxB (a b : BitVec 64) : BitVec 64 := if a ≤ b then a else b

/-- Per-space state: last assigned tx packet number, and largest acked. -/
structure PnState where
  lastPkt : BitVec 64
  largestAcked : BitVec 64

/-- Invariant: the largest acknowledged packet number was actually assigned. -/
def PnInv (s : PnState) : Prop := s.largestAcked ≤ s.lastPkt

/-- Send a packet: assign the next number (no wrap in the QUIC range; guarded by
`hroom`, which holds for every real packet number `< 2^62`). -/
def send (s : PnState) (_hroom : s.lastPkt < s.lastPkt + 1) : PnState :=
  { s with lastPkt := s.lastPkt + 1 }

/-- Process an ACK that claims packet number `ackpn`.  A valid ACK only
acknowledges a sent packet (`ackpn <= lastPkt`, which `ngtcp2_pkt_validate_ack`
enforces); then `largest_acked` advances toward it.  An out-of-range ACK is
ignored. -/
def recvAck (s : PnState) (ackpn : BitVec 64) : PnState :=
  if ackpn ≤ s.lastPkt then { s with largestAcked := maxB s.largestAcked ackpn } else s

theorem send_inv (s : PnState) (hroom : s.lastPkt < s.lastPkt + 1) (h : PnInv s) :
    PnInv (send s hroom) := by
  unfold PnInv send at *; bv_omega

theorem recvAck_inv (s : PnState) (ackpn : BitVec 64) (h : PnInv s) :
    PnInv (recvAck s ackpn) := by
  unfold PnInv recvAck maxB at *; (repeat' split) <;> bv_omega

/-- A packet-number-space event.  `send` carries the no-wrap side condition. -/
inductive Op where
  | send (hroom : Bool)
  | ack  (ackpn : BitVec 64)

/-- Apply an event.  A `send` only advances if there is room (no wrap); otherwise
it is a no-op, so the model is total and faithful (real numbers never wrap). -/
def apply (s : PnState) : Op → PnState
  | .send _ => if h : s.lastPkt < s.lastPkt + 1 then send s h else s
  | .ack e  => recvAck s e

/-- **Packet-number monotonicity invariant (whole state machine)**: from a state
satisfying the invariant, ANY sequence of sends and ACKs keeps
`largest_acked <= last_pkt_num` — ngtcp2 never marks an unsent packet number as
acknowledged, for any history.  By induction. -/
theorem seq_inv (ops : List Op) (s : PnState) (h : PnInv s) :
    PnInv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o with
    | send hr =>
      simp only [apply]; split
      · rename_i hlt; exact send_inv s hlt h
      · exact h
    | ack e => simp only [apply]; exact recvAck_inv s e h

end NgtcpRV.ConnPktNum
