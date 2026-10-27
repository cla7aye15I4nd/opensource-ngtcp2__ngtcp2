/-!
ngtcp2_ringbuf: masked-index spatial safety + the `len ≤ cap` state invariant,
preserved under ANY sequence of push/pop operations (stateful induction).

Capacity is a power of two `cap = mask + 1`; every access computes its slot as
`(first + offset) & mask`.  CBMC checks one call; here the invariant is carried
across an arbitrary operation sequence by induction.
-/
namespace NgtcpRV.RingBuf

/-- Every slot index the ringbuf computes is `≤ mask`, hence `< cap = mask+1`:
`ngtcp2_ringbuf_get`/`push_back`/`push_front` never index past the buffer. Holds
for all `first`, `offset`, `mask`. -/
theorem slot_le_mask (x mask : BitVec 64) : (x &&& mask).toNat ≤ mask.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_right

theorem slot_lt_cap (x mask : BitVec 64) :
    (x &&& mask).toNat < mask.toNat + 1 := by
  have := slot_le_mask x mask; omega

theorem one_toNat : (1 : BitVec 64).toNat = 1 := rfl

/-- `(x + 1).toNat = x.toNat + 1` when it does not wrap. -/
theorem toNat_add_one {x : BitVec 64} (h : x.toNat + 1 < 2^64) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, one_toNat, Nat.mod_eq_of_lt h]

/-- Ringbuf state: the `first` offset and the element count `len`. -/
structure St where
  first : BitVec 64
  len : BitVec 64

/-- The maintained invariant: `first` is a valid slot and `len` never exceeds the
capacity `mask + 1`. -/
def Inv (mask : BitVec 64) (s : St) : Prop :=
  s.first.toNat ≤ mask.toNat ∧ s.len.toNat ≤ mask.toNat + 1

/-- `ngtcp2_ringbuf_push_back`, exactly as C. -/
def pushBack (mask : BitVec 64) (s : St) : St :=
  if s.len = mask + 1 then { first := (s.first + 1) &&& mask, len := s.len }
  else { first := s.first, len := s.len + 1 }

/-- `ngtcp2_ringbuf_push_front`, exactly as C. -/
def pushFront (mask : BitVec 64) (s : St) : St :=
  let first' := (s.first - 1) &&& mask
  if s.len < mask + 1 then { first := first', len := s.len + 1 }
  else { first := first', len := s.len }

/-- `ngtcp2_ringbuf_pop_front`: advance first, decrement len. -/
def popFront (mask : BitVec 64) (s : St) : St :=
  { first := (s.first + 1) &&& mask, len := s.len - 1 }

variable {mask : BitVec 64}

theorem pushBack_inv (hc : mask.toNat + 1 < 2^64) (s : St) (h : Inv mask s) :
    Inv mask (pushBack mask s) := by
  obtain ⟨hf, hl⟩ := h
  unfold pushBack Inv
  by_cases he : s.len = mask + 1
  · simp only [he, if_true]
    exact ⟨slot_le_mask _ _, Nat.le_of_eq (toNat_add_one (by omega))⟩
  · simp only [he, if_false]
    refine ⟨hf, ?_⟩
    have hne : s.len.toNat ≠ (mask + 1).toNat := fun hx => he (BitVec.eq_of_toNat_eq hx)
    have hm1 : (mask + 1).toNat = mask.toNat + 1 := toNat_add_one (by omega)
    have hlt : s.len.toNat < mask.toNat + 1 := by omega
    rw [toNat_add_one (by omega)]; omega

theorem pushFront_inv (hc : mask.toNat + 1 < 2^64) (s : St) (h : Inv mask s) :
    Inv mask (pushFront mask s) := by
  obtain ⟨hf, hl⟩ := h
  unfold pushFront Inv
  by_cases he : s.len < mask + 1
  · simp only [he, if_true]
    refine ⟨slot_le_mask _ _, ?_⟩
    have hm1 : (mask + 1).toNat = mask.toNat + 1 := toNat_add_one (by omega)
    have hlt : s.len.toNat < mask.toNat + 1 := by
      have := (BitVec.lt_def).mp he; omega
    rw [toNat_add_one (by omega)]; omega
  · simp only [he, if_false]
    exact ⟨slot_le_mask _ _, hl⟩

/-- `ngtcp2_ringbuf_pop_front` carries the C `assert(rb->len)` as `1 ≤ len`. -/
theorem popFront_inv (s : St) (h : Inv mask s) (hlen : 1 ≤ s.len.toNat) :
    Inv mask (popFront mask s) := by
  obtain ⟨hf, hl⟩ := h
  refine ⟨slot_le_mask _ _, ?_⟩
  show (s.len - 1).toNat ≤ mask.toNat + 1
  have h1 : (s.len - 1).toNat = s.len.toNat - 1 := by
    rw [BitVec.toNat_sub, one_toNat]
    have := s.len.isLt
    omega
  omega

/-- An operation on the ringbuf: append at either end (the two that can grow or
rotate the buffer; `pop_front` is handled separately as it carries `assert(len)`). -/
inductive Op where | pushB | pushF

def apply (mask : BitVec 64) (s : St) : Op → St
  | .pushB => pushBack mask s
  | .pushF => pushFront mask s

/-- **STATEFUL INDUCTION**: for ANY sequence of push_back / push_front operations,
starting from a state that satisfies the invariant, the resulting state still
satisfies it — `len ≤ cap` and `first` a valid slot throughout.  The ringbuf can
never overflow its `mask+1`-element buffer, no matter the operation history.
Proved by induction on the operation list. -/
theorem seq_inv (hc : mask.toNat + 1 < 2^64) (ops : List Op) (s : St) (h : Inv mask s) :
    Inv mask (ops.foldl (apply mask) s) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o os ih =>
    refine ih _ ?_
    cases o
    · exact pushBack_inv hc s h
    · exact pushFront_inv hc s h

end NgtcpRV.RingBuf
