/-!
Receive-side stream shutdown STATE-MACHINE invariant (strm.c) — dual of
`ConnStrmState`.

The receive-side stream flags are monotone and ordered: receiving RESET_STREAM
also sets SHUT_RD (ngtcp2_strm.h: RESET_STREAM_RECVED "NGTCP2_STRM_FLAG_SHUT_RD is
also set").  So a read-shut or reset-received stream never reverts to readable.
We model the recv-side flags and prove, over ANY transition history: the flags
are monotone and `reset_recved ⇒ shut_rd`.  By induction.
-/
namespace NgtcpRV.ConnStrmRecv

/-- Receive-side stream flags. -/
structure S where
  shutRd : Bool      -- SHUT_RD: no further reception
  resetRecved : Bool -- RESET_STREAM received

/-- Structural invariant: a reset-received stream is also read-shut. -/
def Inv (s : S) : Prop := s.resetRecved = true → s.shutRd = true

/-- `shutdown_read`: set SHUT_RD. -/
def shutRd (s : S) : S := { s with shutRd := true }
/-- receive RESET_STREAM: sets RESET_STREAM_RECVED and (per the header) SHUT_RD. -/
def recvReset (s : S) : S := { s with resetRecved := true, shutRd := true }

inductive Op where
  | shutRd
  | recvReset

def apply (s : S) : Op → S
  | .shutRd    => shutRd s
  | .recvReset => recvReset s

theorem apply_inv (s : S) (o : Op) (_h : Inv s) : Inv (apply s o) := by
  cases o with
  | shutRd => intro _; rfl
  | recvReset => intro _; rfl

theorem apply_monotone (s : S) (o : Op) :
    (s.shutRd = true → (apply s o).shutRd = true) ∧
    (s.resetRecved = true → (apply s o).resetRecved = true) := by
  cases o <;> (unfold apply shutRd recvReset <;> simp)

/-- **Recv-stream-state safety (whole state machine)**: from a valid state, ANY
sequence of transitions keeps `reset_recved ⇒ shut_rd` and the flags monotone —
a read-shut or reset-received stream never becomes readable again.  By induction. -/
theorem seq_inv (ops : List Op) (s : S) (h : Inv s) :
    Inv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih => exact ih _ (apply_inv s o h)

theorem seq_monotone_shutRd (ops : List Op) (s : S) (h : s.shutRd = true) :
    (ops.foldl apply s).shutRd = true := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih => exact ih _ ((apply_monotone s o).1 h)

end NgtcpRV.ConnStrmRecv
