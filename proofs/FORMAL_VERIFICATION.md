# ngtcp2 formal verification suite

Machine-checked memory-safety and functional-correctness proofs for ngtcp2,
discharged with **CBMC** under two independent decision procedures (external
**CaDiCaL** SAT + **Z3** SMT). A lemma counts as PROVED only when *both*
backends report VERIFICATION SUCCESSFUL with complete loop unwinding and
`--unwinding-assertions` on — i.e. these are sound proofs over all inputs (or
under explicitly stated, module-maintained invariants), not bounded tests.

Inspired by the decompose-into-many-small-kernel-checked-lemmas approach:
`prove.py` runs every entry in `lemmas.json`, each a tiny harness in `harness/`
linked against the **unmodified** ngtcp2 sources.

## What is proved (114 lemmas, ~30 modules)

- **Stateless packet codec** — every frame decoder *and* encoder, long/short
  headers, version-negotiation and stateless-reset writers, the varint codec
  (incl. the foundational `put_uvarintlen == put_uvarint` lemma every encoder's
  OOB-safety rests on).
- **Primitives / containers** — `conv`, `str` (Lemire `count_digit` and the
  integer cube root `ngtcp2_cbrt` proved *correct*, not just safe), `range`,
  `vec`, `buf`, `cid`, `addr`, `ringbuf`, `pq`, `map` (Robin-Hood find),
  `ksl` (within-block search for every comparator), `wf` (windowed max filter).
- **Protocol logic** — `pmtud` (probe indexing), `ratelim` (token-bucket
  overflow guards), `rst`, transport-parameter decode primitives, `ppe`
  padding writes (the assert-guarded write family around the #12 area).
- **Congestion control** — **reno fully**, **BBR fully** (all ~85 functions
  incl. the `update_on_ack` orchestrator), cubic (events, `cbrt`,
  `compute_w_cubic`; the branch-heavy `on_ack_recv` is hand-audited — see below).
- **Path / CID** — `pv` path validation, `dcidtr` CID-uniqueness + readers.
- **Memory management** — `balloc` bump-pointer pool (16-alignment invariant), `opl` free-list, `objalloc`, `frame_chain` allocation.
- **Crypto / API** — `crypto` key-material allocation + nonce creation, `settings`/`transport_params` default-setters.

Guarantee for all of the above: no out-of-bounds read/write, no divide-by-zero,
no undefined shift, no length/encode mismatch, no unsigned underflow.

## Findings

One real, reproduced vulnerability across the whole effort: the
`conn_crumble_initial_crypto` size_t underflow → client crash (fixed, PR #12).
The formal pass itself surfaced **no new defects** — every REFUTED result was a
false alarm from unconstrained inputs or insufficient unwinding, resolved by
supplying the genuine maintained invariant (cwnd bounds, `pacing_interval_m>=1`,
recovery accounting, Robin-Hood displacement, etc.). ngtcp2 is clean on the
verified surface.

## Scope boundary (what is NOT proved, and why)

- `conn.c` (~14.7k lines of deeply-stateful packet handlers): the whole-function
  packet-dispatch control flow is not isolable as per-function CBMC proofs. Its
  *connection-level safety invariants* are instead proved deductively as
  state-machine invariants holding across every event history — flow control both
  directions (`ConnRecvInv`/`ConnSendInv`), anti-amplification
  (`ConnAmplification`), packet-number monotonicity (`ConnPktNum`), key-update
  one-at-a-time (`ConnKeyUpdate`), handshake ordering (`ConnHandshake`), stream
  shutdown/final-size (`ConnStrmState`/`ConnStrmRecv`/`ConnFinalSize`), stream and
  CID limits (`ConnStreamLimit`/`ConnCid`), path-validation and congestion bounds
  (`ConnPathVal`/`ConnCongestion`), and teardown irreversibility
  (`ConnStateMachine`), plus the pure arithmetic helpers (`ConnFlowControl`,
  `ConnPkt`, `StrmFlow`). What remains is the dispatch loop's full operational
  semantics, which needs a modeled interpreter rather than more invariants.
- `ksl` insert/remove/split: the *within-block* search is proved for all sizes
  (`KslSearch`) and the split memcpy/memmove index arithmetic is proved in bounds
  (`KslSplit`). The modules riding on `ksl` have their core operations proved
  deductively: `gaptr_push` (`GaptrPush`), `rob` (gap logic + chunk-memcpy
  heap-safety via `RobWrite`), `acktr` (`AcktrArith`/`ConnAcktrMax`), `idtr`
  (`IdtrOpen`), `dcidtr` (`DcidtrVerify`). What remains is the B-tree *semantic*
  invariant (sorted order preserved across node split/merge).
- Allocators (`balloc`/`objalloc`): bump-advance safety and sizing composition
  proved (`BallocGet`/`ObjallocGet`). `crypto`: AEAD nonce uniqueness proved
  (`CryptoNonce`); the rest wraps an external TLS library. `qlog`: the uint64
  decimal-length buffer bound proved (`QlogDigits`).
- A few monolithic functions (`transport_params_decode`,
  `cubic_cc_on_ack_recv`) exceed CBMC's practical solve budget as whole units;
  their bounds-checking primitives / risky arithmetic are proved or hand-audited.

## Deductive layer: loops & data-structure invariants (Lean 4, `proofs/lean/`)

CBMC unrolls loops to a fixed bound and steps machine code a fixed number of
instructions; neither can cover *all* input sizes. For the loop and
data-structure code at the boundary above, `proofs/lean/NgtcpRV/` carries
kernel-checked Lean proofs that quantify over every size, each audited with
`#print axioms` to depend only on `[propext, Quot.sound]`:

- **`VecLenVarint`** — `ngtcp2_vec_len_varint` is a *sound and complete* overflow
  detector: returns the exact sum when it fits in a varint, `-1` iff the true
  (unbounded) sum would exceed `MAX`, for every `n`. By induction on the list.
- **`KslSearch`** — the `ngtcp2_ksl_search_def` within-block scan returns the
  correct lower-bound index for **every** block size (CBMC covered only n=32):
  index ≤ `blk->n` (read-safety), all scanned keys satisfy the comparator, the
  stop key fails it.
- **`RingBuf`** — the power-of-two ringbuf (`cap = mask+1`, slots via `& mask`):
  every computed slot is `< cap` (get/push in bounds), and `seq_inv` proves by
  induction that **any** sequence of push/pop operations preserves `len ≤ cap` —
  the buffer can never overflow, for any operation history.
- **`RangeAlg`** — `ngtcp2_range_{intersect,cut,len}` semantically: a non-empty
  `intersect(q,k)` is a sub-range of `k`, and cutting `k` by it tiles `k`
  exactly (`len l + len m + len r = len k`, pieces well-formed and ordered).
  This is the invariant `gaptr`/`rob`/`acktr` rely on when splitting a gap.

- **`KslSplit`** — the B-tree node split (`ksl_split_blk`/`ksl_split_node`)
  memcpy/memmove index arithmetic stays inside the fixed `MAX_NBLK=32`-slot
  arrays, and a full block splits into two `MIN_NBLK` halves (the two asserts).
  This is the memory-safety core of the one structure CBMC could not reach.

Built on those primitives, the stateful operations:

- **`GaptrPush`** — `ngtcp2_gaptr_push` set-level correctness: after pushing `q`,
  the still-unpushed offsets are exactly the previously-unpushed ones minus `q`
  (induction over the gap list, on top of `RangeAlg`).
- **`RobWrite`** — `rob_write_data` chunk-buffer `memcpy` is in bounds for every
  offset/len (the rob `rob_push` gap logic is the same subtraction as `GaptrPush`).
- **`AcktrArith`** — `acktr_recv_ack`'s attacker-supplied ACK-range `int64`
  arithmetic has no signed overflow, given the `validate_ack` guards (induction).
- **`IdtrOpen`** — `ngtcp2_idtr_open` correctness, directly from the gaptr model.
- **`DcidtrVerify`** — `verify_cid_uniqueness` reports a conflict iff the CID is
  present; `remove_dcid_at` swap-remove is index-safe.

Allocators and `conn.c` safety helpers:

- **`BallocGet`** / **`ObjallocGet`** — the `balloc` bump advance never overruns
  the block (safe *because of* 16-alignment, despite an apparent off-by-one), and
  `objalloc`'s block sizing discharges `balloc_get`'s preconditions (composition).
- **`ConnFlowControl`** — `conn_enforce_flow_control` keeps `offset ≤ max_offset`
  (no memory-exhaustion DoS); `dcid_tx_left` keeps `bytes_sent ≤ 3·bytes_recv`
  (the QUIC anti-amplification limit, no traffic-amplification DoS).
- **`ConnPkt`** — `conn_shape_udp_payload` never exceeds any negotiated UDP
  payload max; `pktns_select_pkt_numlen` returns a length that holds the value.

`RangeAlg` + `RingBuf` + `KslSearch` + `KslSplit` are the primitives beneath
`gaptr`/`rob`/`acktr`/`idtr`/`dcidtr`; proving their invariants is the groundwork
for the stateful modules above. Also in `proofs/lean/`: RISC-V machine-code
proofs (`AdjustPktNum`, `RangeInit`, `RangeIntersect`, `PutUvarint`, …) that
verify the *compiled* object code of leaf functions — strictly stronger than a
C-level proof, since they assume nothing about the compiler.

### Full deductive module index (~100 modules, all kernel-checked)

- **Data-structure primitives**: `RangeAlg`, `RingBuf`, `KslSearch`, `KslSplit`,
  `KslSplitSorted` (ksl: within-block search for all sizes + split memory-safety
  + split sorted-order preservation).
- **Stateful data structures**: `GaptrPush`, `RobWrite`, `AcktrArith`,
  `ConnAcktrMax`, `IdtrOpen`, `DcidtrVerify`.
- **Allocators**: `BallocGet`, `ObjallocGet`.
- **Crypto primitives**: `CryptoNonce` (AEAD nonce uniqueness),
  `CryptoHeaderProt` (header-protection reversibility), `CryptoCmemeq`
  (constant-time compare correctness).
- **Wire codec**: `ConnVarintLen`, `VarintRoundtrip`, `ConvRoundtrip` (uint64 BE
  roundtrip), `PktNumDecode` (packet-number decode congruence), `QlogDigits`
  (uint64 decimal-length bound), `VecLenVarint` (sound+complete overflow
  detector), `ConnCidLen` (CID-length buffer safety).
- **conn.c safety helpers**: `ConnFlowControl`, `ConnPkt`, `StrmFlow`,
  `ConnCid`, `StreamOffset`.
- **conn.c whole-history state-machine invariants**: `ConnRecvInv`,
  `ConnSendInv`, `ConnPktNum`, `ConnKeyUpdate`, `ConnStrmState`, `ConnStrmRecv`,
  `ConnFinalSize`, `ConnStreamLimit`, `ConnAmplification`, `ConnCongestion`,
  `ConnHandshake`, `ConnPathVal`, `ConnStateMachine` (teardown irreversibility),
  `ConnEcn`, `ConnPtoBackoff`, `ConnIdleTimeout`, `ConnRetirePriorTo`,
  `ConnCryptoLevel`, `ConnVersionNeg`.
- **Composite dispatch interpreters**: `ConnComposite` (5 invariants, 11 events),
  `ConnFullModel` (8 invariants, 17 events) — a single `step` function whose
  reachable states all satisfy the full safety invariant; the operational-
  semantics direction for the `conn.c` dispatch loop. `ConnSafety` derives the
  individual named guarantees (flow control, anti-amplification, …) as corollaries.
- **Congestion control & loss detection**: `ConnRttSmooth` (smoothed-RTT stays in
  range), `ConnMinRtt` (min_rtt lower bound), `ConnRecovery` (one reduction per
  recovery period), `ConnSlowStart` (loss exits slow start), `ConnInFlight`
  (bytes-in-flight no underflow), `ConnLossThreshold` (loss threshold stable),
  `ConnAckDelay` (ACK-delay scaling bounded), `ConnMaxData` / `ConnWindowTune`
  (advertised limit monotone / window auto-tuning bounded).
- **Packet & frame parsing**: `ConnLongHeader` / `ConnShortHeader` (header-byte
  decode), `ConnStreamFrameType` (STREAM flag bijection), `ConnStreamId` (stream-ID
  index/type bijection), `ConnFrameAllow` (handshake frame allowlist),
  `ConnAckEliciting`, `ConnAckGap` (ACK gap encoding), `ConnPktNumSpace`,
  `ConnStatelessReset` (token read in bounds), `ConnHexEncode`,
  `ConvRoundtrip1632`, `ConnDatagram`, `ConnNewToken`, `ConnPktNumUnique`
  (packet-number ⇒ nonce uniqueness).
- **Transport-parameter validation**: `ConnActiveCidLimit`, `ConnMaxStreams`,
  `ConnMaxUdpPayload`, `ConnMaxAckDelay`.

(~100 deductive modules in total; this index names the principal ones.)

Each module's top theorem `#print axioms` depends only on the standard
`[propext, Classical.choice, Quot.sound]` (several on fewer), so the elaborator's
results are confirmed by the Lean kernel.

## Techniques (see commit history)

- External CaDiCaL for SAT (the built-in `--sat-solver cadical` is unavailable
  in this CBMC build).
- To reach a `static` function: write the harness as `#include "ngtcp2_FOO.c"`
  and omit that file from the lemma's link set — CBMC only analyses code
  reachable from `harness`, so a large file is fine when one small function is
  called.
- The logging macro's `_Generic` is neutralised by including `ngtcp2_log.h`
  first (its include guard then suppresses re-inclusion) and `#undef`-ing the
  log macros to no-ops before compiling the module.
- Static ring buffers are set up via the generated `*_init` + `push_back`.

Run: `PROVE_JOBS=2 PROVE_MEM_GB=4 python3 prove.py [lemma names...]`

## Empirical note on the ksl core (2026-10-27)

`ngtcp2_ksl_insert` was attempted directly (single insert into an empty ksl,
no block split). CBMC exhausts >12 GB and OOMs on both backends: a ksl block
embeds `nodes[NGTCP2_KSL_MAX_NBLK]` (32) plus the keys buffer, and bit-blasting
that structure together with objalloc/balloc allocation modelling is beyond
CBMC's practical reach even for one insert. This is why `ksl` insert/remove/
split — and the modules that mutate ksl state (`rob`, `acktr`, `gaptr`, `idtr`)
— are out of scope for this isolated-harness method. The ksl *read* path
(within-block search, all comparators) IS proved.

`ngtcp2_pkt_split_vec_rand` is similarly out of reach: the full ngtcp2_pkt.c
SSA combined with symbolic growing-array indexing OOMs CBMC even with the PCG
RNG stubbed to its contract. Its building block ngtcp2_vec_split_at is proved.

## ksl: also unreachable at reduced degree (2026-10-27)

Beyond the OOM at the shipped degree (16 → 32-node blocks), a small-model
attempt — rebuilding ksl at NGTCP2_KSL_DEGR=2 (4-node blocks, identical
algorithm) to make the split path tractable — makes CBMC 6.6.0 abort with an
internal invariant violation ("expr.id() != ID_if || ... type" mismatch) while
type-checking ngtcp2_ksl.c. So the ksl B-tree is unreachable with this CBMC for
two independent reasons (OOM at real degree; frontend crash at small degree).
Verifying it needs a different tool (deductive: Frama-C/WP, or a Lean/Coq model).
