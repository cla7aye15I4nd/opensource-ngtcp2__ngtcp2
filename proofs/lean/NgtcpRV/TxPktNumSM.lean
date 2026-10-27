/-!
# conn.c TX packet-number assignment: strict monotonicity (no reuse) + range bound

Third stateful conn.c subsystem.  Every transmitted packet in a packet-number
space takes its number from `pktns->tx.last_pkt_num`: the number is
`last_pkt_num + 1` and then `++pktns->tx.last_pkt_num` (lib/ngtcp2_conn.c lines
1220, 2885, 4699, 4912, …), starting from `last_pkt_num = initial_pkt_num - 1`
(line 815).  The deliberate packet-number *skip* used to foil optimistic-ACK
attacks (`conn_handle_skip_pkt`) is just an extra `++last_pkt_num`, so it only
widens the gap — it never breaks ordering.  A close-on-exhaustion check
(line 10637: `last_pkt_num == NGTCP2_MAX_PKT_NUM` ⇒ close) keeps numbers within
`[.., NGTCP2_MAX_PKT_NUM]`.

RFC 9000 §12.3 forbids ever reusing a packet number within a space.  We model the
assignment and prove, over any number of emissions (real or skipped), that
`last_pkt_num` strictly increases — so every assigned number is unique and
ordered — and that assigning only while `last < MAX` keeps numbers in range.
-/
namespace NgtcpRV.TxPktNumSM

/-- `NGTCP2_MAX_PKT_NUM = 2^62 - 1` (kept opaque; results hold for its actual value). -/
def MAX_PKT_NUM : Int := 2 ^ 62 - 1

/-- TX state: `last` = `pktns->tx.last_pkt_num` (an `int64_t`, `-1`-based initially). -/
structure St where
  last : Int

/-- Emit one packet (real or a skip): the assigned number is `last + 1`, and the
state advances by one.  Returns `(assigned number, new state)`. -/
def emit (s : St) : Int × St := (s.last + 1, ⟨s.last + 1⟩)

/-- Each emission strictly increases `last_pkt_num`. -/
theorem emit_strict_mono (s : St) : s.last < (emit s).2.last := by
  simp only [emit]; omega

/-- The number handed to a packet is exactly the new `last_pkt_num`. -/
theorem emit_assigns_new_last (s : St) : (emit s).1 = (emit s).2.last := rfl

/-- Replay `n` emissions (real packets and/or skips). -/
def runEmit : St → Nat → St
  | s, 0 => s
  | s, (n + 1) => runEmit (emit s).2 n

/-- After `n` emissions, `last_pkt_num` has advanced by exactly `n`. -/
theorem runEmit_last (s : St) (n : Nat) : (runEmit s n).last = s.last + n := by
  induction n generalizing s with
  | zero => simp [runEmit]
  | succ n ih =>
    rw [runEmit, ih (emit s).2]
    simp only [emit]; omega

/-- `last_pkt_num` is monotone across any run of emissions. -/
theorem runEmit_mono (s : St) (n : Nat) : s.last ≤ (runEmit s n).last := by
  rw [runEmit_last]; omega

/-- The number assigned to the `k`-th future emission from state `s` (0-indexed). -/
def nth (s : St) (k : Nat) : Int := s.last + k + 1

/-- **No reuse / strict ordering**: distinct emissions receive strictly ordered
packet numbers — earlier emissions get strictly smaller numbers, so no packet
number is ever assigned twice within the space. -/
theorem nth_strict_mono (s : St) (j k : Nat) (h : j < k) : nth s j < nth s k := by
  unfold nth; omega

/-- **Range bound**: emitting only while `last < MAX_PKT_NUM` (guaranteed by the
close-on-exhaustion check) keeps every assigned number `≤ NGTCP2_MAX_PKT_NUM`, so
it is always a valid 62-bit packet number. -/
theorem emit_in_range (s : St) (h : s.last < MAX_PKT_NUM) :
    (emit s).1 ≤ MAX_PKT_NUM := by
  simp only [emit]; omega

end NgtcpRV.TxPktNumSM
