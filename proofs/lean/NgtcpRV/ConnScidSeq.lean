/-!
Source-connection-ID sequence numbering (conn.c, RFC 9000 §5.1.1).

Each connection ID an endpoint issues carries a sequence number; ngtcp2 assigns
them from an increasing counter (`scid.last_seq + 1`), so the `k`-th issued CID has
sequence `base + k`.  Sequence numbers are therefore strictly increasing,
contiguous (no gaps), and unique — which `retire_prior_to` and CID retirement rely
on.
-/
namespace NgtcpRV.ConnScidSeq

/-- The sequence number of the `k`-th issued source connection ID. -/
def scidSeq (base k : Nat) : Nat := base + k

/-- Sequence numbers are contiguous: each is one more than the previous. -/
theorem scidSeq_contiguous (base k : Nat) : scidSeq base (k + 1) = scidSeq base k + 1 := by
  unfold scidSeq; omega

/-- Strictly increasing, hence unique: distinct issues get distinct sequences. -/
theorem scidSeq_strict_mono (base i j : Nat) (h : i < j) : scidSeq base i < scidSeq base j := by
  unfold scidSeq; omega

theorem scidSeq_injective (base i j : Nat) (h : scidSeq base i = scidSeq base j) : i = j := by
  unfold scidSeq at h; omega

end NgtcpRV.ConnScidSeq
