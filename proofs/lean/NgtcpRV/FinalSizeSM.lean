/-!
# conn.c stream final-size consistency (RFC 9000 §4.5)

Sixth stateful conn.c subsystem.  On the receive side, `conn_recv_stream` /
`conn_recv_reset_stream` enforce that a stream's *final size* — fixed when a frame
with the FIN bit (or a RESET_STREAM) arrives — is consistent across every frame
(lib/ngtcp2_conn.c:7638):

```c
  if (fr->fin) {
    if (strm->flags & NGTCP2_STRM_FLAG_SHUT_RD) {
      if (strm->rx.last_offset != fr_end_offset) return NGTCP2_ERR_FINAL_SIZE;
    } else if (strm->rx.last_offset > fr_end_offset) return NGTCP2_ERR_FINAL_SIZE;
  } else if ((strm->flags & NGTCP2_STRM_FLAG_SHUT_RD) &&
             strm->rx.last_offset < fr_end_offset) return NGTCP2_ERR_FINAL_SIZE;
```

Once `SHUT_RD` is set, `rx.last_offset` holds the immutable final size.  A
final-size *confusion* (two different finals, or data past the final) was a
recurring QUIC vulnerability class.  We model the receive state and prove, over
ANY sequence of frames, that the final size is immutable once set and no frame is
ever accepted that carries data beyond it.
-/
namespace NgtcpRV.FinalSizeSM

/-- Receive state: `lastOffset` = `rx.last_offset`; `finalSize = some f` once FIN /
RESET_STREAM has fixed the final size (`SHUT_RD`), and then `lastOffset = f`. -/
structure St where
  lastOffset : Nat
  finalSize : Option Nat

/-- Receive a frame ending at `endOff`, `fin` = carries FIN / is RESET_STREAM.
`none` = rejected with `NGTCP2_ERR_FINAL_SIZE`. -/
def recv (s : St) (endOff : Nat) (fin : Bool) : Option St :=
  match s.finalSize, fin with
  | some f, true  => if endOff = f then some s else none
  | some f, false => if endOff ≤ f then some s else none
  | none,   true  =>
      if s.lastOffset ≤ endOff then some { lastOffset := endOff, finalSize := some endOff }
      else none
  | none,   false => some { s with lastOffset := max s.lastOffset endOff }

/-- Invariant: once the final size is known, `rx.last_offset` equals it. -/
def Inv (s : St) : Prop :=
  match s.finalSize with
  | none => True
  | some f => s.lastOffset = f

/-- A single receive preserves the invariant. -/
theorem recv_preserves (s : St) (endOff : Nat) (fin : Bool) (h : Inv s)
    (s' : St) (hr : recv s endOff fin = some s') : Inv s' := by
  unfold recv at hr; unfold Inv at h ⊢
  cases hf : s.finalSize with
  | some f =>
      rw [hf] at hr h
      cases fin with
      | true =>
          simp only at hr; split at hr
          · injection hr with hr; subst hr; rw [hf]; exact h
          · exact absurd hr (by simp)
      | false =>
          simp only at hr; split at hr
          · injection hr with hr; subst hr; rw [hf]; exact h
          · exact absurd hr (by simp)
  | none =>
      rw [hf] at hr
      cases fin with
      | true =>
          simp only at hr; split at hr
          · injection hr with hr; subst hr; rfl
          · exact absurd hr (by simp)
      | false =>
          injection hr with hr; subst hr; trivial

/-- **Final size immutability**: once the final size is `f`, any accepted frame
leaves it `f` — the final size can never be changed after it is set. -/
theorem final_size_immutable (s : St) (f endOff : Nat) (fin : Bool)
    (hf : s.finalSize = some f) (s' : St) (hr : recv s endOff fin = some s') :
    s'.finalSize = some f := by
  unfold recv at hr; rw [hf] at hr
  cases fin with
  | true => simp only at hr; split at hr
            · injection hr with hr; subst hr; exact hf
            · exact absurd hr (by simp)
  | false => simp only at hr; split at hr
             · injection hr with hr; subst hr; exact hf
             · exact absurd hr (by simp)

/-- **No data beyond the final size**: once the final size is `f` (with the
invariant holding), every accepted frame ends at an offset `≤ f`. -/
theorem no_data_beyond_final (s : St) (f endOff : Nat) (fin : Bool)
    (h : Inv s) (hf : s.finalSize = some f) (s' : St)
    (hr : recv s endOff fin = some s') : endOff ≤ f := by
  unfold recv at hr; rw [hf] at hr
  cases fin with
  | true => simp only at hr; split at hr
            · rename_i he; omega
            · exact absurd hr (by simp)
  | false => simp only at hr; split at hr
             · rename_i he; omega
             · exact absurd hr (by simp)

/-- Replay a whole frame sequence, keeping state on rejection. -/
def run (s0 : St) (ops : List (Nat × Bool)) : St :=
  ops.foldl (fun s p => (recv s p.1 p.2).getD s) s0

/-- The invariant holds after ANY sequence of received frames. -/
theorem run_inv (s0 : St) (ops : List (Nat × Bool)) (h : Inv s0) : Inv (run s0 ops) := by
  unfold run
  induction ops generalizing s0 with
  | nil => simpa using h
  | cons p ops ih =>
    simp only [List.foldl_cons]
    refine ih _ ?_
    cases hr : recv s0 p.1 p.2 with
    | none => simpa [hr] using h
    | some s' => simp only [hr, Option.getD]; exact recv_preserves s0 p.1 p.2 h s' hr

end NgtcpRV.FinalSizeSM
