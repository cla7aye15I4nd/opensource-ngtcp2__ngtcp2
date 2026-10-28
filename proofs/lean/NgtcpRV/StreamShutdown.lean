/-!
# conn.c stream shutdown flags are monotone (lib/ngtcp2_strm)

A stream's direction-shutdown is tracked by two bits in `strm->flags`
(ngtcp2_strm.h): `NGTCP2_STRM_FLAG_SHUT_RD = 0x01`, `NGTCP2_STRM_FLAG_SHUT_WR =
0x02`, with `SHUT_RDWR` their union.  Flags are only ever set, via bitwise OR
(`strm->flags |= ...`), never cleared — so a shutdown, once in effect, is permanent,
and a stream reaches the fully-shut state once both directions are shut.

We model the two bits (each `|=` sets its bit and never clears it — the independent
semantics of the bitwise OR) and prove: a set bit stays set under any further
operation; "fully shut" (both bits) is permanent once reached; and shutting both
directions reaches it.  A `decide`-checked lemma ties the Bool model to the real
`uint8` bit operations.
-/
namespace NgtcpRV.StreamShutdown

structure Flags where
  rdShut : Bool
  wrShut : Bool

inductive Op | shutRd | shutWr

def apply (f : Flags) : Op → Flags
  | .shutRd => { f with rdShut := true }
  | .shutWr => { f with wrShut := true }

/-- Fully shut = both directions shut (`flags & SHUT_RDWR == SHUT_RDWR`). -/
def fullyShut (f : Flags) : Bool := f.rdShut && f.wrShut

/-- The read-shutdown bit, once set, stays set under any operation. -/
theorem rd_persists (f : Flags) (op : Op) (h : f.rdShut = true) : (apply f op).rdShut = true := by
  cases op <;> simp [apply, h]

/-- The write-shutdown bit, once set, stays set under any operation. -/
theorem wr_persists (f : Flags) (op : Op) (h : f.wrShut = true) : (apply f op).wrShut = true := by
  cases op <;> simp [apply, h]

/-- **Fully-shut is permanent**: once both directions are shut, no operation reopens
the stream. -/
theorem fully_shut_persists (f : Flags) (op : Op) (h : fullyShut f = true) :
    fullyShut (apply f op) = true := by
  unfold fullyShut at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨rd_persists f op h.1, wr_persists f op h.2⟩

/-- Shutting both directions reaches the fully-shut state. -/
theorem shut_both (f : Flags) : fullyShut (apply (apply f .shutRd) .shutWr) = true := by
  simp [apply, fullyShut]

def run (f0 : Flags) (ops : List Op) : Flags := ops.foldl apply f0

/-- Over any sequence of shutdown operations, a set read-bit stays set. -/
theorem run_rd_persists (f0 : Flags) (ops : List Op) (h : f0.rdShut = true) :
    (run f0 ops).rdShut = true := by
  unfold run
  induction ops generalizing f0 with
  | nil => simpa using h
  | cons op ops ih => simp only [List.foldl_cons]; exact ih _ (rd_persists f0 op h)

/-- Over any sequence, fully-shut stays fully-shut. -/
theorem run_fully_shut_persists (f0 : Flags) (ops : List Op) (h : fullyShut f0 = true) :
    fullyShut (run f0 ops) = true := by
  unfold run
  induction ops generalizing f0 with
  | nil => simpa using h
  | cons op ops ih => simp only [List.foldl_cons]; exact ih _ (fully_shut_persists f0 op h)

/-- Faithfulness to the real `uint8` bits: OR-ing in `SHUT_RD` sets that bit, and the
`SHUT_RDWR` test matches holding both bits (checked over all 256 byte values). -/
theorem bit_model_faithful :
    (∀ f : BitVec 8, (f ||| 1#8) &&& 1#8 = 1#8) ∧
    (∀ f : BitVec 8, (f &&& 3#8 = 3#8) ↔ (f &&& 1#8 = 1#8 ∧ f &&& 2#8 = 2#8)) := by
  decide

end NgtcpRV.StreamShutdown
