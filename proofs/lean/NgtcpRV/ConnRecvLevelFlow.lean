import NgtcpRV.ConnLevelFlow
/-!
Connection-level RECEIVE flow control (conn.c, RFC 9000 §4.1) — receive dual of
`ConnLevelFlow`.

The connection's `rx.offset` is the total data received across all streams and
must stay within the advertised connection limit `rx.max_offset`; otherwise it is
a FLOW_CONTROL_ERROR.  We reuse the `ConnLevelFlow.totalSent` sum (here the total
received) and prove the total received is within the connection receive limit.
-/
namespace NgtcpRV.ConnRecvLevelFlow
open NgtcpRV.ConnLevelFlow

/-- **Total received within the connection limit**: if the connection receive
offset is the sum of per-stream receipts and is within the advertised limit, the
total is too — so a peer cannot exceed connection-level receive credit. -/
theorem total_recv_within_limit (streamRecv : List Nat) (connRxOffset connRxMax : Nat)
    (hacct : connRxOffset = totalSent streamRecv) (hlim : connRxOffset ≤ connRxMax) :
    totalSent streamRecv ≤ connRxMax :=
  total_within_limit streamRecv connRxOffset connRxMax hacct hlim

end NgtcpRV.ConnRecvLevelFlow
