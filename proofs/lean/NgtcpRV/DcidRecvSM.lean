/-!
# conn.c NEW_CONNECTION_ID receive: retire_prior_to monotonicity + bounded seq-gap

Second stateful conn.c subsystem.  `conn_recv_new_connection_id`
(lib/ngtcp2_conn.c) handles an attacker-supplied stream of NEW_CONNECTION_ID
frames `(seq, retire_prior_to)`.  Two invariants protect the endpoint:

  * **retire_prior_to is monotonically non-decreasing.**  `conn->dcid.retire_prior_to`
    is only ever written at `if (rpt < fr->retire_prior_to) rpt = fr->retire_prior_to`
    (line 8243) — it can rise but never fall, so once a sequence number is retired
    it stays retired.

  * **The seq-gap tracker is bounded.**  Each accepted frame pushes `fr->seq` into
    `dcid.seqgap`; then `if (ngtcp2_ksl_len(...) > 32) ngtcp2_gaptr_drop_first_gap(...)`
    (line 8218) caps the number of tracked gaps at 32.  This bounds memory against
    a malicious peer sending sparse/reordered sequence numbers (the attack the
    source comment at line 8255 describes).

Both are proved by induction over arbitrary frame sequences — no bound on how many
frames an attacker sends.
-/
namespace NgtcpRV.DcidRecvSM

/-- Max tracked gaps (`> 32` triggers a drop). -/
def MAXGAP : Nat := 32

/-- Push one sequence number then apply the `len > 32 ⇒ drop` cap: the gap count
rises by at most one, and a push that would reach 33 is immediately dropped to 32. -/
def capPush (n : Nat) : Nat := if n + 1 > MAXGAP then n else n + 1

/-- The relevant connection state: `rpt` = `dcid.retire_prior_to`,
`gaplen` = number of tracked gaps in `dcid.seqgap`. -/
structure St where
  rpt : Nat
  gaplen : Nat

/-- Receiving one accepted NEW_CONNECTION_ID `(seq, frpt)`: raise `retire_prior_to`
to `max rpt frpt` (the C's conditional upward update) and push `seq` into the
capped gap tracker. -/
def recv (s : St) (_seq frpt : Nat) : St :=
  { rpt := max s.rpt frpt, gaplen := capPush s.gaplen }

/-- `capPush` keeps the gap count within the cap. -/
theorem capPush_bounded (n : Nat) (h : n ≤ MAXGAP) : capPush n ≤ MAXGAP := by
  unfold capPush MAXGAP at *; split <;> omega

/-- A single receive never lowers `retire_prior_to`. -/
theorem recv_rpt_mono (s : St) (seq frpt : Nat) : s.rpt ≤ (recv s seq frpt).rpt := by
  simp only [recv]; exact Nat.le_max_left _ _

/-- A single receive keeps the gap count within the cap. -/
theorem recv_gaplen_bounded (s : St) (seq frpt : Nat) (h : s.gaplen ≤ MAXGAP) :
    (recv s seq frpt).gaplen ≤ MAXGAP := by
  simp only [recv]; exact capPush_bounded s.gaplen h

/-- Replay a whole sequence of accepted frames. -/
def runRecv (s0 : St) (ops : List (Nat × Nat)) : St :=
  ops.foldl (fun s p => recv s p.1 p.2) s0

/-- **retire_prior_to monotonicity** over ANY sequence of received frames: the
final `retire_prior_to` is never below the initial one. -/
theorem run_rpt_mono (s0 : St) (ops : List (Nat × Nat)) :
    s0.rpt ≤ (runRecv s0 ops).rpt := by
  unfold runRecv
  induction ops generalizing s0 with
  | nil => simp
  | cons p ops ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (recv_rpt_mono s0 p.1 p.2) (ih (recv s0 p.1 p.2))

/-- **Bounded gap tracker** over ANY sequence of received frames: if the tracker
starts within the cap it stays within the cap, no matter how many frames arrive. -/
theorem run_gaplen_bounded (s0 : St) (ops : List (Nat × Nat)) (h : s0.gaplen ≤ MAXGAP) :
    (runRecv s0 ops).gaplen ≤ MAXGAP := by
  unfold runRecv
  induction ops generalizing s0 with
  | nil => simpa using h
  | cons p ops ih =>
    simp only [List.foldl_cons]
    exact ih (recv s0 p.1 p.2) (recv_gaplen_bounded s0 p.1 p.2 h)

/-- With the frame-level validation `fr->retire_prior_to ≤ fr->seq` (line 8224),
each upward update sets `retire_prior_to` to a value `≤` some received `seq`: a
single receive keeps `rpt ≤ b` whenever the incoming `frpt ≤ b` and `rpt ≤ b`. -/
theorem recv_rpt_le (s : St) (seq frpt b : Nat) (hs : s.rpt ≤ b) (hf : frpt ≤ b) :
    (recv s seq frpt).rpt ≤ b := by
  simp only [recv]; exact Nat.max_le.mpr ⟨hs, hf⟩

end NgtcpRV.DcidRecvSM
