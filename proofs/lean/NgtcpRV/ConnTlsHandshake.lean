/-!
TLS/library handshake-completion ordering (conn.c).

ngtcp2 has two completion flags: NGTCP2_CONN_FLAG_TLS_HANDSHAKE_COMPLETED (the TLS
stack finished) and NGTCP2_CONN_FLAG_HANDSHAKE_COMPLETED (the library finished).
The library only marks the handshake complete after the TLS handshake has
completed, so `HANDSHAKE_COMPLETED ⇒ TLS_HANDSHAKE_COMPLETED`.  Both flags are
set-only.  We prove the ordering invariant holds across any transition history.
-/
namespace NgtcpRV.ConnTlsHandshake

structure Hs where
  tlsCompleted : Bool
  completed : Bool

/-- Ordering invariant: library completion implies TLS completion. -/
def Inv (s : Hs) : Prop := s.completed = true → s.tlsCompleted = true

/-- The TLS stack reports completion. -/
def tlsComplete (s : Hs) : Hs := { s with tlsCompleted := true }
/-- The library marks the handshake complete — only reachable after TLS completion. -/
def complete (s : Hs) : Hs := if s.tlsCompleted then { s with completed := true } else s

inductive Op where | tlsComplete | complete

def apply (s : Hs) : Op → Hs
  | .tlsComplete => tlsComplete s
  | .complete    => complete s

theorem apply_inv (s : Hs) (o : Op) (h : Inv s) : Inv (apply s o) := by
  cases o with
  | tlsComplete => intro _; rfl
  | complete =>
    simp only [apply, complete, Inv]
    split
    · rename_i hc; intro _; exact hc
    · exact h

/-- **Ordering (whole history)**: library completion never precedes TLS
completion, across any transition history. -/
theorem seq_inv (ops : List Op) (s : Hs) (h : Inv s) : Inv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih => exact ih _ (apply_inv s o h)

end NgtcpRV.ConnTlsHandshake
