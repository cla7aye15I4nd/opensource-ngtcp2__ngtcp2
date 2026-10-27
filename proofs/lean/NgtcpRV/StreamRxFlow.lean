/-!
# conn.c stream receive flow control: advertised limits are never exceeded

Fourth stateful conn.c subsystem.  `conn_recv_stream` (lib/ngtcp2_conn.c) enforces
QUIC flow control (RFC 9000 §4) on incoming STREAM data at two levels:

```c
  if (NGTCP2_MAX_VARINT - datalen < fr->offset) return NGTCP2_ERR_FLOW_CONTROL;
  fr_end_offset = fr->offset + datalen;
  if (strm->rx.max_offset < fr_end_offset) return NGTCP2_ERR_FLOW_CONTROL;   // per-stream
  ...
  if (strm->rx.last_offset < fr_end_offset) {
    len = fr_end_offset - strm->rx.last_offset;
    if (conn_max_data_violated(conn, len)) return NGTCP2_ERR_FLOW_CONTROL;    // connection
    conn->rx.offset += len;
  }
```
with `conn_max_data_violated(conn, len)  ==  conn->rx.max_offset - conn->rx.offset < len`.

That connection check is a `uint64_t` subtraction `max_offset - offset`, sound only
because `offset <= max_offset` — exactly the invariant it maintains.  We model both
levels and prove, over ANY sequence of received STREAM frames, that the accepted
state always satisfies `strm.last_offset <= strm.max_offset` and
`conn.offset <= conn.max_offset`: the endpoint never admits more data than it
advertised (bounding receive-buffer memory), and the FC subtraction never
underflows.
-/
namespace NgtcpRV.StreamRxFlow

def MAX_VARINT : Nat := 2 ^ 62 - 1

structure St where
  strmLast : Nat    -- strm->rx.last_offset
  strmMax  : Nat    -- strm->rx.max_offset  (advertised per-stream limit)
  connOff  : Nat    -- conn->rx.offset
  connMax  : Nat    -- conn->rx.max_offset  (advertised connection limit)

def InvStrm (s : St) : Prop := s.strmLast ≤ s.strmMax
def InvConn (s : St) : Prop := s.connOff ≤ s.connMax
def Inv (s : St) : Prop := InvStrm s ∧ InvConn s

/-- Receive one STREAM frame `(frOff, datalen)`; `none` = rejected with
`NGTCP2_ERR_FLOW_CONTROL` (state unchanged), `some s'` = accepted. -/
def recv (s : St) (frOff datalen : Nat) : Option St :=
  if MAX_VARINT < frOff + datalen then none
  else if s.strmMax < frOff + datalen then none
  else if s.strmLast < frOff + datalen then
    if s.connMax - s.connOff < (frOff + datalen) - s.strmLast then none
    else some { s with strmLast := frOff + datalen,
                       connOff := s.connOff + ((frOff + datalen) - s.strmLast) }
  else some s

/-- A single receive preserves both flow-control invariants. -/
theorem recv_preserves (s : St) (frOff datalen : Nat) (h : Inv s)
    (s' : St) (hr : recv s frOff datalen = some s') : Inv s' := by
  obtain ⟨hs, hc⟩ := h
  unfold InvStrm at hs; unfold InvConn at hc
  unfold recv at hr
  split at hr
  · exact absurd hr (by simp)
  · split at hr
    · exact absurd hr (by simp)
    · split at hr
      · split at hr
        · exact absurd hr (by simp)
        · injection hr with hr; subst hr
          refine ⟨?_, ?_⟩
          · show (frOff + datalen) ≤ s.strmMax; omega
          · show s.connOff + ((frOff + datalen) - s.strmLast) ≤ s.connMax; omega
      · injection hr with hr; subst hr; exact ⟨hs, hc⟩

/-- Apply a received frame, keeping the old state when the frame is rejected (a
rejected frame does not mutate flow-control state). -/
def stepKeep (s : St) (f : Nat × Nat) : St := (recv s f.1 f.2).getD s

theorem stepKeep_preserves (s : St) (f : Nat × Nat) (h : Inv s) : Inv (stepKeep s f) := by
  unfold stepKeep
  cases hr : recv s f.1 f.2 with
  | none => simpa using h
  | some s' => simp only [hr, Option.getD]; exact recv_preserves s f.1 f.2 h s' hr

def runRecv (s0 : St) (ops : List (Nat × Nat)) : St := ops.foldl stepKeep s0

/-- **Flow-control safety** over ANY sequence of received STREAM frames: both the
per-stream and the connection-level advertised limits always hold — the endpoint
never admits more data than it advertised. -/
theorem run_inv (s0 : St) (ops : List (Nat × Nat)) (h : Inv s0) : Inv (runRecv s0 ops) := by
  unfold runRecv
  induction ops generalizing s0 with
  | nil => simpa using h
  | cons f ops ih =>
    simp only [List.foldl_cons]
    exact ih (stepKeep s0 f) (stepKeep_preserves s0 f h)

/-- Corollary: the reachable state respects the per-stream limit. -/
theorem stream_limit_respected (s0 : St) (ops : List (Nat × Nat)) (h : Inv s0) :
    (runRecv s0 ops).strmLast ≤ (runRecv s0 ops).strmMax := (run_inv s0 ops h).1

/-- Corollary: the reachable state respects the connection limit. -/
theorem conn_limit_respected (s0 : St) (ops : List (Nat × Nat)) (h : Inv s0) :
    (runRecv s0 ops).connOff ≤ (runRecv s0 ops).connMax := (run_inv s0 ops h).2

/-- The connection FC check is sound/underflow-free: under the maintained invariant
`connOff ≤ connMax`, the C test `connMax - connOff < len` (a `uint64_t`
subtraction) fires exactly when admitting `len` bytes would exceed the limit. -/
theorem fc_check_sound (s : St) (len : Nat) (h : InvConn s) :
    (s.connMax - s.connOff < len) ↔ (s.connMax < s.connOff + len) := by
  unfold InvConn at h; omega

end NgtcpRV.StreamRxFlow
