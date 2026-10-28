import NgtcpRV.DcidRecvSM
/-!
# conn.c NEW_CONNECTION_ID dispatch (lib/ngtcp2_conn.c)

Adds the NEW_CONNECTION_ID handler (`conn_recv_new_connection_id`) to the receive dispatch,
composing `DcidRecvSM`: each accepted frame raises `dcid.retire_prior_to` (monotone) and
pushes a sequence number into the 32-capped gap tracker (DoS bound).  We prove the dispatch
keeps the gap tracker bounded and `retire_prior_to` monotone across any sequence of frames.
-/
namespace NgtcpRV.ConnDispatchCid

open NgtcpRV.DcidRecvSM (capPush MAXGAP capPush_bounded)

structure CS where
  rpt : Nat     -- conn->dcid.retire_prior_to
  gaplen : Nat  -- tracked seq gaps

def Inv (s : CS) : Prop := s.gaplen ≤ MAXGAP

inductive Frame
  | newConnId (seq frpt : Nat)
  | other

def dispatch (s : CS) : Frame → CS
  | .newConnId _ frpt => { rpt := max s.rpt frpt, gaplen := capPush s.gaplen }
  | .other => s

/-- `retire_prior_to` never decreases on a dispatched frame. -/
theorem dispatch_rpt_monotone (s : CS) (f : Frame) : s.rpt ≤ (dispatch s f).rpt := by
  cases f with
  | newConnId seq frpt => show s.rpt ≤ max s.rpt frpt; omega
  | other => exact Nat.le_refl _

/-- The gap tracker stays within the cap. -/
theorem dispatch_preserves (s : CS) (f : Frame) (h : Inv s) : Inv (dispatch s f) := by
  unfold Inv at h ⊢
  cases f with
  | newConnId seq frpt => show capPush s.gaplen ≤ MAXGAP; exact capPush_bounded s.gaplen h
  | other => exact h

def recvPkt (s0 : CS) (frames : List Frame) : CS :=
  frames.foldl dispatch s0

/-- **Gap-tracker bound across any frame sequence** (DoS prevention). -/
theorem recvPkt_preserves (s0 : CS) (frames : List Frame) (h : Inv s0) : Inv (recvPkt s0 frames) := by
  unfold recvPkt
  induction frames generalizing s0 with
  | nil => simpa using h
  | cons f fs ih => simp only [List.foldl_cons]; exact ih _ (dispatch_preserves s0 f h)

/-- **retire_prior_to monotone across any frame sequence** — once a sequence number is
retired it stays retired. -/
theorem recvPkt_rpt_monotone (s0 : CS) (frames : List Frame) : s0.rpt ≤ (recvPkt s0 frames).rpt := by
  unfold recvPkt
  induction frames generalizing s0 with
  | nil => simp
  | cons f fs ih => simp only [List.foldl_cons]; exact Nat.le_trans (dispatch_rpt_monotone s0 f) (ih _)

end NgtcpRV.ConnDispatchCid
