import NgtcpRV.ConnStrmRecv
/-!
Stream receive gate (strm.c / conn.c) — dual of the send gate.

Stream data is accepted only while the receiving side is not read-shut
(`!(flags & NGTCP2_STRM_FLAG_SHUT_RD)`).  SHUT_RD is monotone (`ConnStrmRecv`), so
once a stream is read-shut it never accepts data again across ANY subsequent
history.  We prove the receive gate and its stability.
-/
namespace NgtcpRV.ConnStrmRecvGate
open NgtcpRV.ConnStrmRecv

/-- Data may be accepted iff the stream is not read-shut. -/
def canRecv (s : S) : Bool := !s.shutRd

theorem no_recv_when_shut (s : S) (h : s.shutRd = true) : canRecv s = false := by
  unfold canRecv; simp [h]

/-- **Stable**: once read-shut, no later transition history re-enables receiving. -/
theorem no_recv_after_shut (ops : List Op) (s : S) (h : s.shutRd = true) :
    canRecv (ops.foldl apply s) = false := by
  have := seq_monotone_shutRd ops s h
  unfold canRecv; simp [this]

end NgtcpRV.ConnStrmRecvGate
