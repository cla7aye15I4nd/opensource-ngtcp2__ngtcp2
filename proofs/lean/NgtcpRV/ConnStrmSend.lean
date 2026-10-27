import NgtcpRV.ConnStrmState
/-!
Stream send gate (strm.c / conn.c).

Stream data may be sent only while the stream is not write-shut
(`!(flags & NGTCP2_STRM_FLAG_SHUT_WR)`).  Since SHUT_WR is monotone (proved in
`ConnStrmState`), once a stream is write-shut it can never send again across ANY
subsequent transition history — a closed sending side stays closed.  We prove the
send gate and its stability.
-/
namespace NgtcpRV.ConnStrmSend
open NgtcpRV.ConnStrmState

/-- Data may be sent iff the stream is not write-shut. -/
def canSend (s : S) : Bool := !s.shutWr

/-- No data is sent once the stream is write-shut. -/
theorem no_send_when_shut (s : S) (h : s.shutWr = true) : canSend s = false := by
  unfold canSend; simp [h]

/-- **Stable**: once write-shut, no later transition history can re-enable sending
(`SHUT_WR` only ever gets set). -/
theorem no_send_after_shut (ops : List Op) (s : S) (h : s.shutWr = true) :
    canSend (ops.foldl apply s) = false := by
  have := seq_monotone_shutWr ops s h
  unfold canSend; simp [this]

end NgtcpRV.ConnStrmSend
