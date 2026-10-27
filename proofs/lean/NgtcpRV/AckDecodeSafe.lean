/-!
# ACK-frame decode loop: the validation pass guarantees decode-pass read-safety

`ngtcp2_pkt_decode_ack_frame` (lib/ngtcp2_pkt.c) parses an attacker-controlled
number of ACK ranges in TWO passes over the same bytes:

  * pass 1 (validation, the `for i`/`for j` loop): for each varint, compute its
    on-wire length `n` from the first byte (`ngtcp2_get_uvarintlen`), add it to a
    running `len`, reject if `payloadlen < len`, then advance the cursor by `n`.
  * pass 2 (decode): re-read the SAME varints from `payload+1`, advancing the
    cursor the same way, writing the values out.

Pass 2 performs NO bounds checks of its own; its memory safety rests entirely on
pass 1 having accepted.  We model the shared varint-length sequence and prove, by
induction on it, that if pass 1 accepts then every read pass 2 performs — both
the 1-byte length probe and the full `n`-byte `ngtcp2_get_uvarint` read — lands
inside `[0, payloadlen)`.  This is the spatial read-safety invariant of the loop,
for EVERY range count and every input, with no loop unrolling.  Separately we
pin the write-safety of the `dest->ranges[i]` stores: `i` is capped at
`NGTCP2_MAX_ACK_RANGES = 32`, the size of the backing array.
-/
namespace NgtcpRV.AckDecodeSafe

/-- Pass 1 (validation), exactly as the C: from cursor `off`, for each varint of
on-wire length `n`, require `off + n ≤ payloadlen`, then advance to `off + n`. -/
def Validates (payloadlen : Nat) : Nat → List Nat → Prop
  | _,   []      => True
  | off, n :: ns => off + n ≤ payloadlen ∧ Validates payloadlen (off + n) ns

/-- The reads pass 2 performs: at each varint it first probes 1 byte at `off` (to
learn `n`), then reads the `n` bytes `[off, off+n)`.  Recorded as `(off, n)`. -/
def reads : Nat → List Nat → List (Nat × Nat)
  | _,   []      => []
  | off, n :: ns => (off, n) :: reads (off + n) ns

/-- **Spatial read-safety**: whenever pass 1 accepts, every read pass 2 makes is
in bounds — the `n`-byte read satisfies `off + n ≤ payloadlen`, and (since every
varint on-wire length is `≥ 1`) the 1-byte length probe at `off` satisfies
`off < payloadlen`.  Induction on the varint list; no bound on the range count. -/
theorem reads_in_bounds (payloadlen : Nat) :
    ∀ (off : Nat) (ns : List Nat), Validates payloadlen off ns →
      ∀ p ∈ reads off ns, p.1 + p.2 ≤ payloadlen ∧ (1 ≤ p.2 → p.1 < payloadlen) := by
  intro off ns
  induction ns generalizing off with
  | nil => intro _ p hp; simp only [reads, List.not_mem_nil] at hp
  | cons n ns ih =>
    intro hv p hp
    obtain ⟨hhead, htail⟩ := hv
    simp only [reads, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨hhead, fun _ => by omega⟩
    · exact ih (off + n) htail p hp

/-- Plain recursive total length of the varint sequence (never wraps). -/
def lsum : List Nat → Nat
  | []      => 0
  | n :: ns => n + lsum ns

/-- The decode cursor never runs past `payloadlen`: after reading all validated
varints from `off`, the final cursor `off + Σn` is `≤ payloadlen`.  (This is the
`assert((size_t)(p - payload) == len)` with `len ≤ payloadlen`.) -/
theorem cursor_bounded (payloadlen : Nat) :
    ∀ (off : Nat) (ns : List Nat), off ≤ payloadlen → Validates payloadlen off ns →
      off + lsum ns ≤ payloadlen := by
  intro off ns
  induction ns generalizing off with
  | nil => intro h0 _; simpa [lsum] using h0
  | cons n ns ih =>
    intro _ hv
    obtain ⟨hhead, htail⟩ := hv
    have h := ih (off + n) hhead htail
    simp only [lsum]; omega

/-! ### Write-safety of the `dest->ranges[i]` stores -/

/-- `NGTCP2_MAX_ACK_RANGES`, the size of the backing `ack_ranges[]` array. -/
def MAX_ACK_RANGES : Nat := 32

/-- `max_rangecnt = min(NGTCP2_MAX_ACK_RANGES, rangecnt)`, so every decoded index
`i < max_rangecnt` is a valid index into the 32-element backing array. -/
theorem range_index_in_bounds (rangecnt i : Nat)
    (h : i < min MAX_ACK_RANGES rangecnt) : i < MAX_ACK_RANGES := by
  unfold MAX_ACK_RANGES at *; omega

end NgtcpRV.AckDecodeSafe
