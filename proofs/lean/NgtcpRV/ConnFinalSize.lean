/-!
Stream final-size STATE-MACHINE invariant (strm.c / conn.c).

QUIC fixes a stream's final size when a FIN (or RESET_STREAM) is received; after
that, no byte may be received beyond it, and the final size cannot change
(a violation is FINAL_SIZE_ERROR, RFC 9000 §4.5).  ngtcp2 enforces this in the
STREAM/RESET_STREAM receive handlers.  We model the receive state (whether the
final size is known, its value, and the highest offset seen) and prove the
invariant `final known ⇒ last_offset <= final_size` across ANY receive history —
so ngtcp2 never accepts data past a declared final size.  By induction.
-/
namespace NgtcpRV.ConnFinalSize

/-- Receive-side final-size state. -/
structure RxFin where
  hasFinal : Bool
  finalSize : Nat
  lastOff : Nat

/-- Invariant: if the final size is known, the highest received offset is within it. -/
def Inv (s : RxFin) : Prop := s.hasFinal = true → s.lastOff ≤ s.finalSize

/-- Receive STREAM data ending at `off`.  If a final size is known, data beyond it
is rejected (FINAL_SIZE_ERROR); otherwise the high-water mark advances. -/
def recvData (s : RxFin) (off : Nat) : RxFin :=
  if s.hasFinal = true ∧ off > s.finalSize then s
  else { s with lastOff := max s.lastOff off }

/-- Receive a FIN declaring final size `fsize`.  Valid only once and only if it is
at least the data already seen (else FINAL_SIZE_ERROR); it then fixes the final
size. -/
def recvFin (s : RxFin) (fsize : Nat) : RxFin :=
  if s.hasFinal = true then s
  else if fsize < s.lastOff then s
  else { hasFinal := true, finalSize := fsize, lastOff := s.lastOff }

theorem recvData_inv (s : RxFin) (off : Nat) (h : Inv s) : Inv (recvData s off) := by
  unfold Inv recvData at *
  split
  · exact h
  · rename_i hcond
    intro hf
    show max s.lastOff off ≤ s.finalSize
    simp only [not_and, Nat.not_lt] at hcond
    have hoff := hcond hf
    have hlast := h hf
    omega

theorem recvFin_inv (s : RxFin) (fsize : Nat) (h : Inv s) : Inv (recvFin s fsize) := by
  unfold Inv recvFin at *
  split
  · exact h
  · split
    · exact h
    · rename_i h1 h2
      intro _
      show s.lastOff ≤ fsize
      omega

/-- A receive event. -/
inductive Op where
  | data (off : Nat)
  | fin  (fsize : Nat)

def apply (s : RxFin) : Op → RxFin
  | .data off  => recvData s off
  | .fin fsize => recvFin s fsize

/-- **Final-size safety (whole state machine)**: from a valid state, ANY sequence
of data receipts and FINs keeps `final known ⇒ last_offset <= final_size` —
ngtcp2 never accepts stream data beyond a declared final size, for any history.
By induction. -/
theorem seq_inv (ops : List Op) (s : RxFin) (h : Inv s) :
    Inv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o with
    | data off  => exact recvData_inv s off h
    | fin fsize => exact recvFin_inv s fsize h

end NgtcpRV.ConnFinalSize
