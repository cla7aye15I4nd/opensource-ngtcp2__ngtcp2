/-!
ngtcp2_acktr_recv_ack: the ACK-range int64 arithmetic cannot overflow.

acktr_recv_ack decodes attacker-supplied ACK ranges with signed arithmetic
    min_ack      = largest_ack - first_ack_range
    largest_ack' = min_ack - gap - 2
    min_ack'     = largest_ack' - len
Running it is sound only because the caller first checks
`ngtcp2_pkt_validate_ack(fr) == 0`, which walks the SAME recurrence and, before
each subtraction, verifies the accumulator is large enough (`>= gap+2`, `>= len`)
so it never goes negative.  All wire values are varints in `[0, 2^62)`.  We model
the shared recurrence and prove: under the validate_ack guards every intermediate
stays in `[0, 2^62)` (hence well inside the int64 range `(-2^63, 2^63)`), so the
signed arithmetic in acktr_recv_ack has no undefined behaviour.
-/
namespace NgtcpRV.Acktr

/-- `2^62`, the varint ceiling; every wire value (`largest_ack`, `first_ack_range`,
each `gap`, each `len`) is in `[0, 2^62)`. -/
def B62 : Int := 2 ^ 62
/-- Signed 64-bit open bounds; a value in `(I64LO, I64HI)` is representable. -/
def I64LO : Int := -(2 ^ 63)
def I64HI : Int := 2 ^ 63

/-- One ACK range from the wire: a gap and a length, each a `< 2^62` varint. -/
structure AckRange where
  gap : Int
  len : Int
  gap_lo : 0 ≤ gap
  gap_hi : gap < B62
  len_lo : 0 ≤ len
  len_hi : len < B62

/-- The recurrence step shared by validate_ack and acktr_recv_ack. -/
def step (acc : Int) (r : AckRange) : Int := acc - (r.gap + 2) - r.len

/-- The validate_ack guards for one step: the accumulator admits the two
subtractions without going negative (exactly the two `< ... return ACK_FRAME`
checks in ngtcp2_pkt_validate_ack). -/
def guard (acc : Int) (r : AckRange) : Prop :=
  r.gap + 2 ≤ acc ∧ r.len ≤ acc - (r.gap + 2)

/-- **No int64 overflow, one step**: if `acc ∈ [0, 2^62)` and the guards hold, then
the two intermediate results computed in acktr_recv_ack
(`largest_ack' = acc - gap - 2` and `min_ack' = largest_ack' - len`) are both in
the representable int64 range `(-2^63, 2^63)`, and `min_ack'` is again in
`[0, 2^62)`. -/
theorem step_no_overflow (acc : Int) (r : AckRange)
    (hlo : 0 ≤ acc) (hhi : acc < B62) (hg : guard acc r) :
    I64LO < acc - r.gap - 2 ∧ acc - r.gap - 2 < I64HI ∧
    I64LO < step acc r ∧ step acc r < I64HI ∧
    0 ≤ step acc r ∧ step acc r < B62 := by
  obtain ⟨hg1, hg2⟩ := hg
  have hgl := r.gap_lo; have hgh := r.gap_hi; have hll := r.len_lo; have hlh := r.len_hi
  unfold step B62 I64LO I64HI at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **No int64 overflow, whole frame**: folding the recurrence over every ACK
range keeps the accumulator in `[0, 2^62)` — so, as long as the validate_ack
guards hold at each step (which `ngtcp2_pkt_validate_ack == 0` guarantees), the
entire ACK-range decode in acktr_recv_ack is free of signed overflow. Proved by
induction on the range list. -/
def guardsHold : Int → List AckRange → Prop
  | _, [] => True
  | acc, r :: rs => guard acc r ∧ guardsHold (step acc r) rs

theorem fold_in_range (rs : List AckRange) :
    ∀ acc : Int, 0 ≤ acc → acc < B62 → guardsHold acc rs →
      0 ≤ rs.foldl step acc ∧ rs.foldl step acc < B62 := by
  induction rs with
  | nil => intro acc h0 hb _; exact ⟨h0, hb⟩
  | cons r rs ih =>
    intro acc h0 hb hg
    obtain ⟨hgr, hgrest⟩ := hg
    have hstep := step_no_overflow acc r h0 hb hgr
    simp only [List.foldl_cons]
    exact ih (step acc r) hstep.2.2.2.2.1 hstep.2.2.2.2.2 hgrest

end NgtcpRV.Acktr
