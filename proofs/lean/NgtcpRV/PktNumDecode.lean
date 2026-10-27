/-!
Packet-number decode congruence (pkt.c `ngtcp2_pkt_adjust_pkt_num`, RFC 9000 A.3).

A received packet carries only the low `k` bits of the packet number; the
receiver reconstructs the full value from the expected packet number:
    candidate = (expected & ~(win-1)) | truncated       (win = 2^k)
    result    = candidate, or candidate + win, or candidate - win  (closest to expected)
Decode is correct only if the reconstructed number carries the SAME low `k` bits
that were transmitted — i.e. `result ≡ truncated (mod win)`.  We prove exactly
this congruence for all three branches.  (`KslSplit`/the machine-code proofs cover
the function's memory safety; this is its functional correctness.)
-/
namespace NgtcpRV.PktNumDecode

/-- `candidate` with the low `k` bits cleared from `expected` and replaced by
`truncated` (`truncated < win`): `(expected & ~(win-1)) | truncated`. -/
def candidate (expected truncated win : Nat) : Nat := expected / win * win + truncated

/-- The candidate carries exactly the transmitted low bits. -/
theorem candidate_mod (expected truncated win : Nat) (ht : truncated < win) :
    candidate expected truncated win % win = truncated := by
  unfold candidate
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

/-- **Decode congruence**: every branch of the reconstruction (`candidate`,
`candidate + win`, `candidate - win` when `candidate ≥ win`) yields a packet
number congruent to the transmitted `truncated` modulo `win` — so decode preserves
the low `k` bits exactly. -/
theorem decode_congruent (expected truncated win : Nat) (ht : truncated < win) :
    candidate expected truncated win % win = truncated ∧
    (candidate expected truncated win + win) % win = truncated ∧
    (win ≤ candidate expected truncated win →
      (candidate expected truncated win - win) % win = truncated) := by
  have hc := candidate_mod expected truncated win ht
  refine ⟨hc, ?_, ?_⟩
  · rw [Nat.add_mod_right]; exact hc
  · intro hge
    have heq : candidate expected truncated win
        = (candidate expected truncated win - win) + win := by omega
    rw [heq, Nat.add_mod_right] at hc
    exact hc

end NgtcpRV.PktNumDecode
