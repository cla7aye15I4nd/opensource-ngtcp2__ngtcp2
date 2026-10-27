/-!
Receive-side flow control & reorder-buffer anti-fragmentation (conn.c / strm.c).

* conn_should_send_max_data / conn_should_send_max_stream_data decide whether to
  grant more credit by `window < 4 * (unsent_max_offset - max_offset)`.  The
  subtraction needs `unsent_max_offset >= max_offset` (offsets only advance), and
  `4 * inc` must not overflow — true because QUIC offsets are `< 2^62`.
* strm_rob_heavily_fragmented bounds the number of reorder-buffer gaps (a
  memory-exhaustion defence) using `span = last_offset - rx_offset`, which needs
  `last_offset >= rx_offset`.
Modelled over `BitVec 64` (uint64, exact wraparound).
-/
namespace NgtcpRV.StrmFlow

/-- `2^62`, the QUIC offset ceiling (varint max + 1). -/
def B62 : BitVec 64 := 0x4000000000000000#64

/-- **Window-update arithmetic is sound**: with the maintained invariant
`max_offset <= unsent_max_offset` and offsets `< 2^62`, the increment
`inc = unsent_max_offset - max_offset` does not underflow, and `4 * inc` does not
overflow `uint64` — so the `window < 4*inc` decision compares the true values. -/
theorem window_update_safe (unsent maxoff : BitVec 64)
    (hinv : maxoff ≤ unsent) (hb : unsent < B62) :
    (unsent - maxoff).toNat = unsent.toNat - maxoff.toNat ∧
    (4#64 * (unsent - maxoff)).toNat = 4 * (unsent - maxoff).toNat := by
  unfold B62 at hb
  constructor
  · bv_omega
  · bv_omega

/-- **Reorder-buffer span is sound**: with the maintained invariant
`rx_offset <= last_offset`, `span = last_offset - rx_offset` does not underflow,
so the fragmentation bound `ngap > 128 + span / MIN_STREAM_DATALEN` is computed on
the true span. -/
theorem frag_span_safe (last rxoff : BitVec 64) (hinv : rxoff ≤ last) :
    (last - rxoff).toNat = last.toNat - rxoff.toNat := by bv_omega

/-- The anti-fragmentation predicate itself (ngap bound).  When it is *false* —
the buffer is not flagged heavily fragmented — the gap count is within the
allowance, bounding reorder-buffer memory. -/
def heavilyFragmented (ngap span minLen : Nat) : Bool :=
  decide (ngap ≥ 4000) || decide (ngap > 128 + span / minLen)

theorem not_fragmented_bounds (ngap span minLen : Nat)
    (h : heavilyFragmented ngap span minLen = false) :
    ngap < 4000 ∧ ngap ≤ 128 + span / minLen := by
  unfold heavilyFragmented at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le, Nat.not_lt] at h
  omega

end NgtcpRV.StrmFlow
