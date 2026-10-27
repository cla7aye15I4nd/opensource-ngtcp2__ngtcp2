/-!
Stream send-state STATE-MACHINE invariant (strm.c).

A stream's lifecycle flags (NGTCP2_STRM_FLAG_*) are monotone: the handlers only
ever SET bits, never clear them, and setting RESET_STREAM also sets SHUT_WR (see
ngtcp2_strm.h: "NGTCP2_STRM_FLAG_SHUT_WR is also set").  So a stream that is
write-shut stays write-shut, and a reset stream is always write-shut.  We model
the send-side flags and prove, across ANY sequence of transitions: the flags are
monotone (a closed stream never reopens) and the structural invariant
`reset ⇒ shut_wr` holds.  By induction.
-/
namespace NgtcpRV.ConnStrmState

/-- Send-side stream flags we track. -/
structure S where
  shutWr : Bool   -- SHUT_WR: no further transmission
  reset : Bool    -- RESET_STREAM sent

/-- Structural invariant: a reset stream is also write-shut. -/
def Inv (s : S) : Prop := s.reset = true → s.shutWr = true

/-- `shutdown_write`: set SHUT_WR. -/
def shutWr (s : S) : S := { s with shutWr := true }
/-- `send RESET_STREAM`: sets RESET_STREAM and (per the header) SHUT_WR. -/
def sendReset (s : S) : S := { s with reset := true, shutWr := true }

/-- A send-side stream transition. -/
inductive Op where
  | shutWr
  | sendReset

def apply (s : S) : Op → S
  | .shutWr    => shutWr s
  | .sendReset => sendReset s

/-- Every transition keeps the structural invariant. -/
theorem apply_inv (s : S) (o : Op) (_h : Inv s) : Inv (apply s o) := by
  cases o <;> (unfold Inv apply shutWr sendReset at * <;> simp_all)

/-- Every transition is monotone: a set bit stays set (no flag is ever cleared). -/
theorem apply_monotone (s : S) (o : Op) :
    (s.shutWr = true → (apply s o).shutWr = true) ∧
    (s.reset = true → (apply s o).reset = true) := by
  cases o <;> (unfold apply shutWr sendReset <;> simp)

/-- **Stream-state safety (whole state machine)**: from a valid state, ANY
sequence of transitions keeps the invariant `reset ⇒ shut_wr`, and the flags stay
monotone — a write-shut or reset stream never reverts.  By induction. -/
theorem seq_inv (ops : List Op) (s : S) (h : Inv s) :
    Inv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih => exact ih _ (apply_inv s o h)

/-- Monotonicity over a whole history: once write-shut, always write-shut. -/
theorem seq_monotone_shutWr (ops : List Op) (s : S) (h : s.shutWr = true) :
    (ops.foldl apply s).shutWr = true := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih => exact ih _ ((apply_monotone s o).1 h)

end NgtcpRV.ConnStrmState
