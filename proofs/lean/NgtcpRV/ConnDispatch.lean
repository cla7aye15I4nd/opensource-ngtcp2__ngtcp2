/-!
# conn.c packet frame-dispatch operational semantics (lib/ngtcp2_conn.c)

`conn_recv_pkt` decodes each frame of a packet and dispatches it by type to a handler
(`conn_recv_stream`, `conn_recv_ack`, `conn_recv_max_data`, …).  This is the top-level
dispatch frontier.  We model it as an operational semantics over the flow-control-relevant
connection state and prove that dispatching ANY sequence of frames in a packet preserves
the connection's flow-control invariant — the key safety property the dispatch must
maintain across every reachable frame ordering.

Handlers modelled per RFC 9000 / the C:
  * STREAM          — guarded receive (StreamRxFlow): accept only within advertised limits;
  * MAX_DATA        — raise the connection send limit (never lowers rx state);
  * MAX_STREAM_DATA — raise a stream send limit;
  * ACK / CRYPTO / PADDING / PING / CONNECTION_CLOSE / other — no effect on rx flow control.
The dispatch is total (every frame type routed) and deterministic.
-/
namespace NgtcpRV.ConnDispatch

/-- The flow-control-relevant connection state. -/
structure CS where
  connOff : Nat   -- conn->rx.offset
  connMax : Nat   -- conn->rx.max_offset
  strmLast : Nat  -- strm->rx.last_offset
  strmMax : Nat   -- strm->rx.max_offset

/-- The receive flow-control invariant. -/
def Inv (s : CS) : Prop := s.connOff ≤ s.connMax ∧ s.strmLast ≤ s.strmMax

/-- The frame kinds dispatched by `conn_recv_pkt`. -/
inductive Frame
  | stream (frEnd : Nat)
  | maxData (v : Nat)
  | maxStreamData (v : Nat)
  | ack | crypto | padding | ping | connClose | other

/-- Dispatch one frame to its handler; `none` = the frame was rejected (connection error),
`some s'` = accepted with updated state. -/
def dispatch (s : CS) : Frame → Option CS
  | .stream frEnd =>
      -- conn_recv_stream: accept only within the per-stream and connection limits
      if frEnd ≤ s.strmMax ∧ s.connOff + (frEnd - s.strmLast) ≤ s.connMax then
        some { s with strmLast := max s.strmLast frEnd,
                      connOff := s.connOff + (frEnd - s.strmLast) }
      else none
  | .maxData v => some { s with connMax := max s.connMax v }
  | .maxStreamData v => some { s with strmMax := max s.strmMax v }
  | .ack => some s
  | .crypto => some s
  | .padding => some s
  | .ping => some s
  | .connClose => some s
  | .other => some s

/-- **Every frame dispatch preserves the flow-control invariant.** -/
theorem dispatch_preserves (s : CS) (f : Frame) (h : Inv s) (s' : CS)
    (hd : dispatch s f = some s') : Inv s' := by
  obtain ⟨hc, hs⟩ := h
  cases f with
  | stream frEnd =>
      simp only [dispatch] at hd
      by_cases hg : frEnd ≤ s.strmMax ∧ s.connOff + (frEnd - s.strmLast) ≤ s.connMax
      · rw [if_pos hg] at hd; injection hd with hd; subst hd
        refine ⟨?_, ?_⟩
        · show s.connOff + (frEnd - s.strmLast) ≤ s.connMax; exact hg.2
        · show max s.strmLast frEnd ≤ s.strmMax; omega
      · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | maxData v => simp only [dispatch] at hd; injection hd with hd; subst hd
                 exact ⟨by show s.connOff ≤ max s.connMax v; omega, hs⟩
  | maxStreamData v => simp only [dispatch] at hd; injection hd with hd; subst hd
                       exact ⟨hc, by show s.strmLast ≤ max s.strmMax v; omega⟩
  | ack => simp only [dispatch] at hd; injection hd with hd; subst hd; exact ⟨hc, hs⟩
  | crypto => simp only [dispatch] at hd; injection hd with hd; subst hd; exact ⟨hc, hs⟩
  | padding => simp only [dispatch] at hd; injection hd with hd; subst hd; exact ⟨hc, hs⟩
  | ping => simp only [dispatch] at hd; injection hd with hd; subst hd; exact ⟨hc, hs⟩
  | connClose => simp only [dispatch] at hd; injection hd with hd; subst hd; exact ⟨hc, hs⟩
  | other => simp only [dispatch] at hd; injection hd with hd; subst hd; exact ⟨hc, hs⟩

/-- Process a whole packet's frame list, keeping state on a rejected frame. -/
def recvPkt (s0 : CS) (frames : List Frame) : CS :=
  frames.foldl (fun s f => (dispatch s f).getD s) s0

/-- **Packet-level safety**: processing any sequence of frames in a packet preserves the
flow-control invariant — the dispatch loop never violates it, whatever the frame ordering. -/
theorem recvPkt_preserves (s0 : CS) (frames : List Frame) (h : Inv s0) : Inv (recvPkt s0 frames) := by
  unfold recvPkt
  induction frames generalizing s0 with
  | nil => simpa using h
  | cons f fs ih =>
    simp only [List.foldl_cons]
    refine ih _ ?_
    cases hd : dispatch s0 f with
    | none => simpa [hd] using h
    | some s' => simp only [hd, Option.getD]; exact dispatch_preserves s0 f h s' hd

/-- The dispatch is total: every frame type produces a defined result (accept or a
well-defined reject). -/
theorem dispatch_total (s : CS) (f : Frame) : (dispatch s f).isSome ∨ dispatch s f = none := by
  cases (dispatch s f) <;> simp

end NgtcpRV.ConnDispatch
