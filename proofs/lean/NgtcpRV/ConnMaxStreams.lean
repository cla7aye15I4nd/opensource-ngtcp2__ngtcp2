/-!
MAX_STREAMS bound (conn.c, RFC 9000 §4.6 / §19.11).

A MAX_STREAMS frame may grant at most `2^60` streams; a larger value is a
FRAME_ENCODING_ERROR.  This bound keeps every stream ID below `2^62` (stream IDs
are `4*n + type`), so stream IDs remain valid QUIC varints.  We prove a validated
`max_streams` keeps all stream IDs in range.
-/
namespace NgtcpRV.ConnMaxStreams

def MAX_STREAMS_LIMIT : Nat := 2 ^ 60

/-- The MAX_STREAMS validation: the granted count must not exceed `2^60`. -/
def validMaxStreams (n : Nat) : Bool := decide (n ≤ MAX_STREAMS_LIMIT)

/-- A validated `max_streams` is at most `2^60`. -/
theorem accepted_bounded (n : Nat) (h : validMaxStreams n = true) : n ≤ 2 ^ 60 := by
  unfold validMaxStreams MAX_STREAMS_LIMIT at h; simpa using h

/-- **Stream IDs stay in range**: with a validated `max_streams`, every stream ID
`4*k + type` (for `k < max_streams`, `type < 4`) is below `2^62` — a valid QUIC
stream ID. -/
theorem stream_id_in_range (n k t : Nat) (h : validMaxStreams n = true)
    (hk : k < n) (ht : t < 4) : 4 * k + t < 2 ^ 62 := by
  have hb := accepted_bounded n h
  have : (2:Nat) ^ 62 = 4 * 2 ^ 60 := by decide
  omega

end NgtcpRV.ConnMaxStreams
