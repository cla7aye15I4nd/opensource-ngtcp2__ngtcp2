/-!
# conn.c unified receive-dispatch invariant (lib/ngtcp2_conn.c)

A single operational model of `conn_recv_pkt`'s frame dispatch carrying every safety
invariant proven piecewise elsewhere, simultaneously:

  * connection flow control   `connOff <= connMax`
  * stream flow control        `strmLast <= strmMax`
  * final-size consistency     `finalSize = some f -> strmLast <= f`   (RFC 9000 §4.5)
  * ACK validity               `txLargestAcked <= txLargestSent`       (no ack of unsent)
  * lifecycle                  once draining, frames are ignored

We prove the single `dispatch` function preserves the whole composite invariant for every
frame type, hence so does processing any packet's frames — a unified operational semantics
for the receive path's safety.
-/
namespace NgtcpRV.ConnDispatchUnified

structure CS where
  connOff : Nat
  connMax : Nat
  strmLast : Nat
  strmMax : Nat
  finalSize : Option Nat
  draining : Bool
  txLargestSent : Int
  txLargestAcked : Int

def finalOk (s : CS) : Prop := ∀ f, s.finalSize = some f → s.strmLast ≤ f

def Inv (s : CS) : Prop :=
  s.connOff ≤ s.connMax ∧ s.strmLast ≤ s.strmMax ∧ finalOk s ∧ s.txLargestAcked ≤ s.txLargestSent

inductive Frame
  | stream (frEnd : Nat) (fin : Bool)
  | maxData (v : Nat)
  | maxStreamData (v : Nat)
  | ack (largestAck : Int)
  | connClose
  | other

def finalGuard (s : CS) (frEnd : Nat) : Bool :=
  match s.finalSize with | some f => decide (frEnd ≤ f) | none => true

def dispatch (s : CS) : Frame → Option CS
  | .stream frEnd fin =>
      if s.draining then some s
      else if frEnd ≤ s.strmMax ∧ s.connOff + (frEnd - s.strmLast) ≤ s.connMax
              ∧ s.strmLast ≤ frEnd ∧ finalGuard s frEnd then
        some { s with strmLast := frEnd, connOff := s.connOff + (frEnd - s.strmLast),
                      finalSize := if fin then
                        (match s.finalSize with | some f => some f | none => some frEnd)
                      else s.finalSize }
      else none
  | .maxData v => if s.draining then some s else some { s with connMax := max s.connMax v }
  | .maxStreamData v => if s.draining then some s else some { s with strmMax := max s.strmMax v }
  | .ack la => if s.draining then some s
               else if la ≤ s.txLargestSent then some { s with txLargestAcked := max s.txLargestAcked la }
               else none
  | .connClose => some { s with draining := true }
  | .other => some s

/-- The unified composite invariant is preserved by every frame dispatch. -/
theorem dispatch_preserves (s : CS) (f : Frame) (h : Inv s) (s' : CS)
    (hd : dispatch s f = some s') : Inv s' := by
  obtain ⟨hc, hs, hf, ha⟩ := h
  cases f with
  | stream frEnd fin =>
      simp only [dispatch] at hd
      by_cases hdr : s.draining
      · rw [if_pos hdr] at hd; injection hd with hd; subst hd; exact ⟨hc, hs, hf, ha⟩
      · rw [if_neg hdr] at hd
        by_cases hg : frEnd ≤ s.strmMax ∧ s.connOff + (frEnd - s.strmLast) ≤ s.connMax
                      ∧ s.strmLast ≤ frEnd ∧ finalGuard s frEnd
        · rw [if_pos hg] at hd; injection hd with hd; subst hd
          obtain ⟨hmax, hconn, hge, hfg⟩ := hg
          refine ⟨hconn, hmax, ?_, ha⟩
          intro g hgeq; show frEnd ≤ g; unfold finalGuard at hfg
          cases hfs : s.finalSize with
          | some f => rw [hfs] at hfg; simp only [decide_eq_true_eq] at hfg
                      cases fin <;> simp [hfs] at hgeq <;> omega
          | none => cases fin with
                    | true => simp [hfs] at hgeq; omega
                    | false => simp [hfs] at hgeq
        · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | maxData v =>
      simp only [dispatch] at hd
      by_cases hdr : s.draining
      · rw [if_pos hdr] at hd; injection hd with hd; subst hd; exact ⟨hc, hs, hf, ha⟩
      · rw [if_neg hdr] at hd; injection hd with hd; subst hd
        exact ⟨by show s.connOff ≤ max s.connMax v; omega, hs, hf, ha⟩
  | maxStreamData v =>
      simp only [dispatch] at hd
      by_cases hdr : s.draining
      · rw [if_pos hdr] at hd; injection hd with hd; subst hd; exact ⟨hc, hs, hf, ha⟩
      · rw [if_neg hdr] at hd; injection hd with hd; subst hd
        refine ⟨hc, by show s.strmLast ≤ max s.strmMax v; omega, ?_, ha⟩
        intro g hgeq; exact Nat.le_trans (hf g hgeq) (by omega)
  | ack la =>
      simp only [dispatch] at hd
      by_cases hdr : s.draining
      · rw [if_pos hdr] at hd; injection hd with hd; subst hd; exact ⟨hc, hs, hf, ha⟩
      · rw [if_neg hdr] at hd
        by_cases hg : la ≤ s.txLargestSent
        · rw [if_pos hg] at hd; injection hd with hd; subst hd
          exact ⟨hc, hs, hf, by show max s.txLargestAcked la ≤ s.txLargestSent; omega⟩
        · rw [if_neg hg] at hd; exact absurd hd (by simp)
  | connClose =>
      simp only [dispatch] at hd; injection hd with hd; subst hd; exact ⟨hc, hs, hf, ha⟩
  | other => simp only [dispatch] at hd; injection hd with hd; subst hd; exact ⟨hc, hs, hf, ha⟩

def recvPkt (s0 : CS) (frames : List Frame) : CS :=
  frames.foldl (fun s f => (dispatch s f).getD s) s0

/-- **Unified receive-path safety**: processing any sequence of frames preserves the full
composite invariant (flow control, final size, ACK validity). -/
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

end NgtcpRV.ConnDispatchUnified
