/-!
Full handshake-progression chain (conn.c).

Consolidating `ConnTlsHandshake` and `ConnHandshake`: the three handshake flags
are ordered TLS_COMPLETED ⟸ HANDSHAKE_COMPLETED ⟸ HANDSHAKE_CONFIRMED.  Each can
only be set after the one it depends on, so `confirmed ⇒ completed ⇒ tls`.  We
model all three in one state machine and prove the chained invariant holds across
any history — in particular `confirmed ⇒ tls` (you never confirm before TLS even
finished).
-/
namespace NgtcpRV.ConnHandshakeChain

structure Hs where
  tls : Bool
  completed : Bool
  confirmed : Bool

/-- The chained ordering invariant. -/
def Inv (s : Hs) : Prop :=
  (s.confirmed = true → s.completed = true) ∧ (s.completed = true → s.tls = true)

def tlsDone (s : Hs) : Hs := { s with tls := true }
def complete (s : Hs) : Hs := if s.tls then { s with completed := true } else s
def confirm (s : Hs) : Hs := if s.completed then { s with confirmed := true } else s

inductive Op where | tlsDone | complete | confirm

def apply (s : Hs) : Op → Hs
  | .tlsDone  => tlsDone s
  | .complete => complete s
  | .confirm  => confirm s

theorem apply_inv (s : Hs) (o : Op) (h : Inv s) : Inv (apply s o) := by
  obtain ⟨h1, h2⟩ := h
  cases o with
  | tlsDone => exact ⟨fun hc => h1 hc, fun _ => rfl⟩
  | complete =>
    simp only [apply, complete, Inv]; split
    · rename_i hc; exact ⟨fun _ => rfl, fun _ => hc⟩
    · exact ⟨h1, h2⟩
  | confirm =>
    simp only [apply, confirm, Inv]; split
    · rename_i hc; exact ⟨fun _ => hc, h2⟩
    · exact ⟨h1, h2⟩

/-- **Chained ordering (whole history)**: from a valid state, any sequence of
events keeps `confirmed ⇒ completed ⇒ tls`. -/
theorem seq_inv (ops : List Op) (s : Hs) (h : Inv s) : Inv (ops.foldl apply s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih => exact ih _ (apply_inv s o h)

/-- Corollary: confirmation implies TLS completion (never confirm before TLS). -/
theorem confirmed_implies_tls (ops : List Op) (s : Hs) (h : Inv s)
    (hc : (ops.foldl apply s).confirmed = true) : (ops.foldl apply s).tls = true :=
  let ⟨h1, h2⟩ := seq_inv ops s h
  h2 (h1 hc)

end NgtcpRV.ConnHandshakeChain
