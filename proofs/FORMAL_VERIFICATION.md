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

## What is proved (105 lemmas, ~28 modules)

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

- `conn.c` (~14.7k lines of deeply-stateful packet handlers) is not isolable as
  per-function CBMC proofs; it needs deductive / invariant-based verification.
- `ksl` insert/remove/split (B-tree rebalancing + dynamic allocation) and the
  modules riding on it (`rob` reassembly, `acktr`, `gaptr`, `idtr`).
- A few monolithic functions (`transport_params_decode`,
  `cubic_cc_on_ack_recv`) exceed CBMC's practical solve budget as whole units;
  their bounds-checking primitives / risky arithmetic are proved or hand-audited.

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
