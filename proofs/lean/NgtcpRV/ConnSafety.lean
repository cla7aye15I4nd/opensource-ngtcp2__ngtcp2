import NgtcpRV.ConnFullModel
/-!
Connection safety corollaries — named end-to-end guarantees derived from the
composite interpreter (`ConnFullModel`).

`ConnFullModel.seq_inv` proves that every reachable connection state (after ANY
dispatch event history) satisfies the full 8-part invariant.  Here we extract the
individually meaningful safety guarantees as named corollaries, so the composite
model's single induction discharges all of them at once for arbitrary histories.
-/
namespace NgtcpRV.ConnSafety
open NgtcpRV.ConnFullModel

variable (evs : List Ev) (c : Conn) (h : Inv c)
include h

/-- Receive flow control is never violated: the highest received offset stays
within the advertised maximum, after any history. -/
theorem receive_flow_control_safe : (evs.foldl step c).rxLast ≤ (evs.foldl step c).rxMax :=
  (seq_inv evs c h).1

/-- Send flow control is never violated. -/
theorem send_flow_control_safe : (evs.foldl step c).txOff ≤ (evs.foldl step c).txMax :=
  (seq_inv evs c h).2.1

/-- No unsent packet is ever acknowledged. -/
theorem no_unsent_ack : (evs.foldl step c).largestAcked ≤ (evs.foldl step c).lastPkt :=
  (seq_inv evs c h).2.2.1

/-- Anti-amplification (3x) is never violated. -/
theorem anti_amplification_safe : (evs.foldl step c).bytesSent ≤ 3 * (evs.foldl step c).bytesRecv :=
  (seq_inv evs c h).2.2.2.1

/-- The stream-concurrency limit is never exceeded. -/
theorem stream_limit_safe : (evs.foldl step c).streamsOpened ≤ (evs.foldl step c).maxStreams :=
  (seq_inv evs c h).2.2.2.2.2.1

/-- The congestion window never collapses below its floor. -/
theorem cwnd_floor_safe : (evs.foldl step c).minCwnd ≤ (evs.foldl step c).cwnd :=
  (seq_inv evs c h).2.2.2.2.2.2.1

/-- The rate-limiter bucket never over-fills. -/
theorem ratelimit_safe : (evs.foldl step c).tokens ≤ (evs.foldl step c).burst :=
  (seq_inv evs c h).2.2.2.2.2.2.2.1

end NgtcpRV.ConnSafety
