/-!
# conn.c stream-ID limit: a peer can open at most `max_streams` streams

Seventh stateful conn.c subsystem.  When a remote-initiated stream first appears,
`conn_recv_stream` rejects it unless its ordinal fits the advertised limit
(lib/ngtcp2_conn.c:7567):

```c
  if (conn->rx.bidi.max_streams < ngtcp2_ord_stream_id(fr->stream_id))
    return NGTCP2_ERR_STREAM_LIMIT;
```
with `ngtcp2_ord_stream_id(sid) = (sid >> 2) + 1` — the 1-based ordinal of the
stream within its type.  The limit is raised only upward (MAX_STREAMS frames,
`conn_recv_max_streams`: `if (max_streams < fr->max_streams) max_streams = ...`),
and capped at `NGTCP2_MAX_STREAMS = 2^60`.

So the number of streams a peer may open is bounded by `max_streams` — the DoS
guard against unbounded stream creation.  We prove the ordinal bound, the stream-id
value bound it implies, limit monotonicity, and the `2^60` cap.
-/
namespace NgtcpRV.StreamIdLimit

/-- `NGTCP2_MAX_STREAMS = 2^60` (kept opaque; the cap result holds for its value). -/
def MAX_STREAMS : Nat := 2 ^ 60

/-- `ngtcp2_ord_stream_id`: the 1-based ordinal `(sid >> 2) + 1`. -/
def ord (sid : Nat) : Nat := sid / 4 + 1

/-- The advertised limit state (`rx.*.max_streams`). -/
structure St where
  maxStreams : Nat

/-- A remote stream is accepted iff its ordinal fits the limit. -/
def accepted (s : St) (sid : Nat) : Prop := ord sid ≤ s.maxStreams

/-- MAX_STREAMS / extension: raise the limit (upward only). -/
def raiseMax (s : St) (v : Nat) : St := { s with maxStreams := max s.maxStreams v }

/-- Every stream ordinal is `≥ 1`. -/
theorem ord_pos (sid : Nat) : 1 ≤ ord sid := by unfold ord; omega

/-- `ord` is monotone in the stream id. -/
theorem ord_mono {a b : Nat} (h : a ≤ b) : ord a ≤ ord b := by unfold ord; omega

/-- Consecutive same-type stream ids (4 apart) have consecutive ordinals, so
distinct same-type streams get distinct ordinals. -/
theorem ord_step (sid : Nat) : ord (sid + 4) = ord sid + 1 := by unfold ord; omega

/-- **Ordinal bound**: an accepted stream's ordinal lies in `[1, max_streams]`, so
at most `max_streams` distinct streams are acceptable (the DoS bound). -/
theorem accepted_ord_range (s : St) (sid : Nat) (h : accepted s sid) :
    1 ≤ ord sid ∧ ord sid ≤ s.maxStreams := ⟨ord_pos sid, h⟩

/-- **Stream-id value bound**: an accepted stream id is `< 4 * max_streams`, so the
peer cannot name streams beyond the advertised window. -/
theorem accepted_sid_bound (s : St) (sid : Nat) (h : accepted s sid) :
    sid < 4 * s.maxStreams := by
  unfold accepted ord at h; omega

/-- Raising the limit never lowers it (MAX_STREAMS is monotone). -/
theorem raiseMax_mono (s : St) (v : Nat) : s.maxStreams ≤ (raiseMax s v).maxStreams := by
  show s.maxStreams ≤ max s.maxStreams v; omega

/-- A stream accepted under the old limit stays acceptable after a raise. -/
theorem accepted_stable (s : St) (v sid : Nat) (h : accepted s sid) :
    accepted (raiseMax s v) sid := by
  unfold accepted at h ⊢; show ord sid ≤ max s.maxStreams v; omega

/-- The `2^60` cap is preserved: a frame with `fr->max_streams ≤ MAX_STREAMS`
(enforced at line 8168) keeps the limit within `NGTCP2_MAX_STREAMS`. -/
theorem raiseMax_capped (s : St) (v : Nat) (hs : s.maxStreams ≤ MAX_STREAMS)
    (hv : v ≤ MAX_STREAMS) : (raiseMax s v).maxStreams ≤ MAX_STREAMS := by
  show max s.maxStreams v ≤ MAX_STREAMS; omega

end NgtcpRV.StreamIdLimit
