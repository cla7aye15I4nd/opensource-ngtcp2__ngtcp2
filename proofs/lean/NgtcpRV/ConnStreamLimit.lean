/-!
Stream-concurrency-limit STATE-MACHINE invariant (conn.c).

A peer may open at most `max_streams` streams of a given type; exceeding it is a
STREAM_LIMIT_ERROR (RFC 9000 §4.6).  ngtcp2 advertises `rx.{bidi,uni}.max_streams`
(raised monotonically — a MAX_STREAMS frame that would lower it is ignored,
conn.c `if (max < rx.max_streams) ...`) and rejects a remote stream whose index
is past the limit.  The invariant is `opened <= max_streams`: a peer can never
open more streams than granted (stream-exhaustion defence).  Proved across ANY
grant/open history, by induction.
-/
namespace NgtcpRV.ConnStreamLimit

/-- Remote-stream accounting: the advertised limit and the number opened. -/
structure SlState where
  maxStreams : Nat
  opened : Nat

/-- Invariant: opened streams are within the advertised limit. -/
def SlInv (s : SlState) : Prop := s.opened ≤ s.maxStreams

/-- Advertise a higher limit; the value only rises (a lower MAX_STREAMS is ignored). -/
def grant (s : SlState) (newMax : Nat) : SlState :=
  if s.maxStreams < newMax then { s with maxStreams := newMax } else s

/-- A peer opens a new stream; accepted only within the limit, else rejected
(STREAM_LIMIT_ERROR). -/
def openStream (s : SlState) : SlState :=
  if s.opened < s.maxStreams then { s with opened := s.opened + 1 } else s

theorem grant_inv (s : SlState) (newMax : Nat) (h : SlInv s) : SlInv (grant s newMax) := by
  unfold SlInv at h
  unfold SlInv grant
  split
  · rename_i hc; show s.opened ≤ newMax; omega
  · exact h

theorem openStream_inv (s : SlState) (h : SlInv s) : SlInv (openStream s) := by
  unfold SlInv openStream at *
  split
  · rename_i hc; show s.opened + 1 ≤ s.maxStreams; omega
  · exact h

inductive Op where
  | grant (newMax : Nat)
  | openStrm

def apply (s : SlState) : Op → SlState
  | .grant m   => grant s m
  | .openStrm  => openStream s

/-- **Stream-limit safety (whole state machine)**: from a valid state, ANY
sequence of limit grants and stream opens keeps `opened <= max_streams` — a peer
can never open more streams than advertised, for any history.  By induction. -/
theorem seq_inv (ops : List Op) (s : SlState) (h : SlInv s) :
    SlInv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o with
    | grant m   => exact grant_inv s m h
    | openStrm  => exact openStream_inv s h

end NgtcpRV.ConnStreamLimit
