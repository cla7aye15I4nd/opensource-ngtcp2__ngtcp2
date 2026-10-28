/-!
# conn.c dispatch with a composite invariant: flow control + final size

Enriching the conn.c receive-dispatch model (`conn_recv_stream`) with a second invariant:
once a stream's final size is established (a FIN or RESET_STREAM), no received data may
exceed it (RFC 9000 §4.5), and the final size is immutable.  We carry both the flow-control
state and the optional final size, and prove the STREAM handler preserves the *composite*
invariant `connOff <= connMax ∧ strmLast <= strmMax ∧ (finalSize = some f → strmLast <= f)`,
hence so does processing any sequence of frames.
-/
namespace NgtcpRV.ConnDispatchFinal

structure CS where
  connOff : Nat
  connMax : Nat
  strmLast : Nat
  strmMax : Nat
  finalSize : Option Nat

/-- The final size, once set, bounds the received data offset. -/
def finalOk (s : CS) : Prop := ∀ f, s.finalSize = some f → s.strmLast ≤ f

def Inv (s : CS) : Prop := s.connOff ≤ s.connMax ∧ s.strmLast ≤ s.strmMax ∧ finalOk s

inductive Frame
  | stream (frEnd : Nat) (fin : Bool)
  | maxData (v : Nat)
  | other

/-- Does the frame's end offset respect an already-known final size? -/
def finalGuard (s : CS) (frEnd : Nat) : Bool :=
  match s.finalSize with
  | some f => decide (frEnd ≤ f)
  | none => true

/-- STREAM handler plus the trivial ones. -/
def dispatch (s : CS) : Frame → Option CS
  | .stream frEnd fin =>
      if frEnd ≤ s.strmMax ∧ s.connOff + (frEnd - s.strmLast) ≤ s.connMax
         ∧ s.strmLast ≤ frEnd ∧ finalGuard s frEnd then
        some { s with strmLast := frEnd,
                      connOff := s.connOff + (frEnd - s.strmLast),
                      finalSize := if fin then
                        (match s.finalSize with | some f => some f | none => some frEnd)
                      else s.finalSize }
      else none
  | .maxData v => some { s with connMax := max s.connMax v }
  | .other => some s

theorem dispatch_preserves (s : CS) (f : Frame) (h : Inv s) (s' : CS)
    (hd : dispatch s f = some s') : Inv s' := by
  obtain ⟨hc, hs, hf⟩ := h
  cases f with
  | stream frEnd fin =>
      simp only [dispatch] at hd
      by_cases hg : frEnd ≤ s.strmMax ∧ s.connOff + (frEnd - s.strmLast) ≤ s.connMax
                    ∧ s.strmLast ≤ frEnd ∧ finalGuard s frEnd
      · rw [if_pos hg] at hd; injection hd with hd; subst hd
        obtain ⟨hmax, hconn, hge, hfg⟩ := hg
        refine ⟨?_, ?_, ?_⟩
        · show s.connOff + (frEnd - s.strmLast) ≤ s.connMax; exact hconn
        · show frEnd ≤ s.strmMax; exact hmax
        · -- finalOk of the new state
          intro g hgeq
          unfold finalGuard at hfg
          cases hfs : s.finalSize with
          | some f =>
              -- new finalSize = some f (fin or not); new strmLast = frEnd ≤ f
              rw [hfs] at hfg; simp only [decide_eq_true_eq] at hfg
              show frEnd ≤ g
              cases fin <;> simp only [hfs] at hgeq <;> injection hgeq with hgeq <;> omega
          | none =>
              -- new finalSize = (if fin then some frEnd else none); new strmLast = frEnd
              cases fin with
              | true => simp only [hfs] at hgeq; injection hgeq with hgeq; subst hgeq; show frEnd ≤ frEnd; omega
              | false => simp [hfs] at hgeq
      · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | maxData v =>
      simp only [dispatch] at hd; injection hd with hd; subst hd
      refine ⟨?_, hs, hf⟩
      show s.connOff ≤ max s.connMax v; omega
  | other => simp only [dispatch] at hd; injection hd with hd; subst hd; exact ⟨hc, hs, hf⟩

def recvPkt (s0 : CS) (frames : List Frame) : CS :=
  frames.foldl (fun s f => (dispatch s f).getD s) s0

/-- The composite invariant holds across any packet's frames. -/
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

end NgtcpRV.ConnDispatchFinal
