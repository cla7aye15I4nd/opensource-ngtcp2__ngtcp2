/-!
ngtcp2_buf invariant (buf.c) — pos <= last <= end.

`ngtcp2_buf` holds `begin <= pos <= last <= end`; `pos..last` is written data,
`last..end` is free space.  Every encoder advances `last` by at most the free
space `ngtcp2_buf_left = end - last`.  We model the state and the operations and
prove the invariant `pos <= last <= end` is preserved across ANY sequence of
resets and (guarded) advances — so a write never runs past the buffer end.
-/
namespace NgtcpRV.ConnBuf

structure Buf where
  pos : Nat
  last : Nat
  endp : Nat

/-- The buffer invariant: written region within the buffer. -/
def BufInv (b : Buf) : Prop := b.pos ≤ b.last ∧ b.last ≤ b.endp

/-- `ngtcp2_buf_left`: free space. -/
def left (b : Buf) : Nat := b.endp - b.last

/-- Advance `last` by `n` — only if there is room (`n <= left`), else no-op. -/
def advance (b : Buf) (n : Nat) : Buf :=
  if n ≤ left b then { b with last := b.last + n } else b

/-- `ngtcp2_buf_reset`: rewind `last` to `pos` (free the written region). -/
def reset (b : Buf) : Buf := { b with last := b.pos }

theorem advance_inv (b : Buf) (n : Nat) (h : BufInv b) : BufInv (advance b n) := by
  unfold BufInv advance left at *; split <;> (first | omega | (simp only []; omega))

theorem reset_inv (b : Buf) (h : BufInv b) : BufInv (reset b) := by
  unfold BufInv reset at *; simp only []; omega

inductive Op where
  | advance (n : Nat)
  | reset

def apply (b : Buf) : Op → Buf
  | .advance n => advance b n
  | .reset     => reset b

/-- **Buffer safety (whole history)**: from a valid buffer, ANY sequence of
advances and resets keeps `pos <= last <= end` — no write ever runs past the
buffer. By induction. -/
theorem seq_inv (ops : List Op) (b : Buf) (h : BufInv b) : BufInv (ops.foldl apply b) := by
  induction ops generalizing b with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o with
    | advance n => exact advance_inv b n h
    | reset     => exact reset_inv b h

end NgtcpRV.ConnBuf
