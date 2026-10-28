/-!
# conn.c dispatch × lifecycle: draining absorbs frames (lib/ngtcp2_conn.c)

Extending `ConnDispatch` with the connection lifecycle: receiving a CONNECTION_CLOSE frame
moves the connection into the draining period (`conn->state = NGTCP2_CS_DRAINING`), and
while draining `conn_recv_pkt` no longer processes incoming frames (the connection is
dead).  We model the frame dispatch together with a `draining` flag and prove: a
CONNECTION_CLOSE enters draining; once draining, every further frame is a no-op; draining
persists across the rest of the packet; and the flow-control invariant is preserved
throughout.
-/
namespace NgtcpRV.ConnDispatchState

structure CS where
  connOff : Nat
  connMax : Nat
  strmLast : Nat
  strmMax : Nat
  draining : Bool

def Inv (s : CS) : Prop := s.connOff ≤ s.connMax ∧ s.strmLast ≤ s.strmMax

inductive Frame
  | stream (frEnd : Nat)
  | maxData (v : Nat)
  | maxStreamData (v : Nat)
  | connClose
  | other

/-- Dispatch one frame, honouring the draining period. -/
def dispatch (s : CS) (f : Frame) : Option CS :=
  if s.draining then some s
  else match f with
    | .connClose => some { s with draining := true }
    | .stream frEnd =>
        if frEnd ≤ s.strmMax ∧ s.connOff + (frEnd - s.strmLast) ≤ s.connMax then
          some { s with strmLast := max s.strmLast frEnd,
                        connOff := s.connOff + (frEnd - s.strmLast) }
        else none
    | .maxData v => some { s with connMax := max s.connMax v }
    | .maxStreamData v => some { s with strmMax := max s.strmMax v }
    | .other => some s

/-- **Draining absorbs**: while draining, every frame dispatch is a no-op. -/
theorem draining_noop (s : CS) (f : Frame) (h : s.draining = true) : dispatch s f = some s := by
  unfold dispatch; rw [if_pos h]

/-- A CONNECTION_CLOSE enters the draining period. -/
theorem connClose_enters_draining (s : CS) (h : s.draining = false) :
    ∃ s', dispatch s .connClose = some s' ∧ s'.draining = true := by
  refine ⟨{ s with draining := true }, ?_, rfl⟩
  unfold dispatch; rw [if_neg (by simp [h])]

/-- Every dispatch preserves the flow-control invariant. -/
theorem dispatch_preserves (s : CS) (f : Frame) (h : Inv s) (s' : CS)
    (hd : dispatch s f = some s') : Inv s' := by
  obtain ⟨hc, hs⟩ := h
  unfold dispatch at hd
  by_cases hdr : s.draining
  · rw [if_pos hdr] at hd; injection hd with hd; subst hd; exact ⟨hc, hs⟩
  · rw [if_neg hdr] at hd
    cases f with
    | connClose => simp only at hd; injection hd with hd; subst hd; exact ⟨hc, hs⟩
    | stream frEnd =>
        simp only at hd
        by_cases hg : frEnd ≤ s.strmMax ∧ s.connOff + (frEnd - s.strmLast) ≤ s.connMax
        · rw [if_pos hg] at hd; injection hd with hd; subst hd
          exact ⟨by show s.connOff + (frEnd - s.strmLast) ≤ s.connMax; exact hg.2,
                 by show max s.strmLast frEnd ≤ s.strmMax; omega⟩
        · rw [if_neg hg] at hd; exact absurd hd (by simp)
    | maxData v => simp only at hd; injection hd with hd; subst hd
                   exact ⟨by show s.connOff ≤ max s.connMax v; omega, hs⟩
    | maxStreamData v => simp only at hd; injection hd with hd; subst hd
                         exact ⟨hc, by show s.strmLast ≤ max s.strmMax v; omega⟩
    | other => simp only at hd; injection hd with hd; subst hd; exact ⟨hc, hs⟩

/-- Dispatch never clears the draining flag (no resurrection). -/
theorem draining_persists_step (s : CS) (f : Frame) (h : s.draining = true) (s' : CS)
    (hd : dispatch s f = some s') : s'.draining = true := by
  rw [draining_noop s f h] at hd; injection hd with hd; subst hd; exact h

def recvPkt (s0 : CS) (frames : List Frame) : CS :=
  frames.foldl (fun s f => (dispatch s f).getD s) s0

/-- **Packet-level**: processing any frame list preserves the flow-control invariant. -/
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

/-- **Draining persists across the whole packet**: once draining, no frame resurrects the
connection. -/
theorem recvPkt_draining_persists (s0 : CS) (frames : List Frame) (h : s0.draining = true) :
    (recvPkt s0 frames).draining = true := by
  unfold recvPkt
  induction frames generalizing s0 with
  | nil => simpa using h
  | cons f fs ih =>
    simp only [List.foldl_cons, draining_noop s0 f h, Option.getD]
    exact ih s0 h

end NgtcpRV.ConnDispatchState
