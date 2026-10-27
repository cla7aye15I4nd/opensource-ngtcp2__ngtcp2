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

## What is proved (99 lemmas, ~25 modules)

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
