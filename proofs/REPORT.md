# Formal verification of ngtcp2 with CBMC

## Approach

This follows the approach of Anthropic's September 2026 Lean formalization of
Fermat's Last Theorem by Claude agents. The proof was split into many small
lemmas, each one was machine-checked, and the whole was re-checked by
independent kernels. Here:

* Each **lemma** is a CBMC harness in `harness/`. It states a property of the
  **unmodified ngtcp2 C sources** in `lib/`, quantified over all inputs (up to
  a stated length bound for buffers).
* Every lemma also checks memory safety and undefined behaviour:
  `--bounds-check --pointer-check --signed-overflow-check
  --pointer-overflow-check --undefined-shift-check --div-by-zero-check`.
  It also checks every `assert()` inside ngtcp2 and checks that all loops
  are fully unwound (`--unwinding-assertions`).
* Each lemma is discharged by **two independent backends**: CBMC's SAT backend
  (CaDiCaL) and Z3 via SMT-LIB2. A lemma is `PROVED` only if both report
  success. `DISAGREE` (one proves, one refutes) would be a soundness alarm.
  `INCOMPLETE` means one backend hit a time or memory limit.
* `ngtcp2_unreachable()` is stubbed as a failing assertion
  (`stubs/unreachable.c`). Otherwise CBMC's model of `abort()` would silently
  prune those paths.

## Running

```sh
cd proofs
PROVE_JOBS=2 PROVE_MEM_GB=6 ./prove.py            # all lemmas
PROVE_JOBS=2 PROVE_MEM_GB=6 ./prove.py frame_ack  # one lemma
```

`prove.py` runs at most `PROVE_JOBS` solver processes and caps each at
`PROVE_MEM_GB` GB of address space. A single frame-decoder lemma peaks at
about 3 GB. Results are written to `results.json` as each lemma finishes.
Tested with CBMC 6.6.0 and Z3 4.16.0.

## Finding: incorrect assertion in `ngtcp2_pkt_adjust_pkt_num`

Lemma `pkt_adjust_pkt_num_rfc` was **refuted by both backends** on the
original code:

```
[ngtcp2_pkt_adjust_pkt_num.assertion.1] assertion cand <= NGTCP2_MAX_VARINT - win: FAILURE
max_pkt_num = 4611686018427387902 (NGTCP2_MAX_PKT_NUM - 1)
pkt_num     = 1006690231 (0x3C00DFB7), pkt_numlen = 4
```

`repro/adjust_pkt_num.c` reproduces it natively:

* Build with assertions enabled: `Assertion 'cand <= NGTCP2_MAX_VARINT - win'
  failed`, and the process aborts.
* Build with `-DNDEBUG`: the function returns 0x400000003C00DFB7, which is
  greater than `NGTCP2_MAX_PKT_NUM`. Both callers in `ngtcp2_conn.c` then
  discard the packet. Release builds are not affected.

The packet number is chosen by the remote endpoint. Reaching a
`max_pkt_num` this close to 2^62 needs an authenticated peer that sends
about 2^31 packets. A 4-byte packet number advances the decoded value by
at most 2^31 per packet. Impact is therefore limited to builds with
assertions enabled, and the severity is low.

The assertion is wrong, not the arithmetic. Returning a value larger than
`NGTCP2_MAX_PKT_NUM` is already part of the contract:
`tests/ngtcp2_pkt_test.c` checks that
`ngtcp2_pkt_adjust_pkt_num(NGTCP2_MAX_PKT_NUM, 0, 1) == 1 << 62`.
`cand + win` cannot overflow `int64_t` (`cand < expected <= 2^62`,
`win <= 2^32`). **Fix:** remove the assertion. A regression test was added.

After the fix, both backends prove two lemmas:

* `pkt_adjust_pkt_num_rfc`: for every `max_pkt_num` in
  `[-1, NGTCP2_MAX_PKT_NUM]`, every length 1–4 and every truncated value, the
  result agrees with the reference algorithm of RFC 9000 Appendix A.3 whenever
  it is `<= NGTCP2_MAX_PKT_NUM`. A result above that is always rejected by the
  caller. The result always keeps the received low bits.
* `pkt_adjust_pkt_num_recovers`: if the sender's true packet number `P` lies
  in `(expected - hwin, expected + hwin]`, decoding its truncation returns
  exactly `P`. This is the guarantee RFC 9000 §17.1 relies on.

## Lemma catalogue

| Lemma | Statement |
|---|---|
| `conv_uvarint_roundtrip` | For every `n < 2^62`: varint put→get round-trips, the length matches `put_uvarintlen` and `get_uvarintlen`, and the encoding is minimal (RFC 9000 §16) |
| `conv_uvarint_decode_safe` | For every byte string of the advertised length, varint decoding reads exactly that many bytes and yields a value `< 2^62` |
| `conv_pkt_num_roundtrip` | 1–4 byte packet number put→get equals `x mod 2^(8·len)`, big-endian |
| `conv_be_ints` | 16/24/32/64-bit big-endian put/get are inverses and match network byte order byte by byte |
| `conv_uvarint30` | The 4-byte Length field encoding decodes back to `n` |
| `pkt_adjust_pkt_num_rfc` | See above |
| `pkt_adjust_pkt_num_recovers` | See above |
| `frame_<type>` (24 instances of `frame_decode_safe`) | For every payload of `1..MAXLEN` adversarial bytes starting with that frame type: no OOB read, UB or assert failure. Returns `NGTCP2_ERR_FRAME_ENCODING` or a length `1 <= rv <= payloadlen`. Every pointer returned (stream/crypto/datagram data, NEW_TOKEN token, CONNECTION_CLOSE reason) lies inside `payload[0, rv)`. ACK `rangecnt <= NGTCP2_MAX_ACK_RANGES`; NEW_CONNECTION_ID CID length 1–20; unknown frame types are rejected |
| `hd_long_decode_safe` | Long header decoding of every input `<= 64` bytes is memory safe. Header length `<= pktlen`, CIDs `<= 20` bytes, token inside the header and only on Initial packets |
| `hd_short_decode_safe` | Short header decoding is memory safe for every legal DCID length and returns `1 + dcidlen` |
| `version_cid_decode_safe` | `ngtcp2_pkt_decode_version_cid` is memory safe for datagrams up to 1500 bytes, which covers the "unsupported version, long CID" path. Reported CIDs lie inside the datagram |
| `pkt_validate_ack_sound` | If `ngtcp2_pkt_validate_ack` accepts (up to 4 ranges, varint values), every acknowledged range is a non-empty interval inside `[min_pkt_num, largest_ack]`, with gaps of at least one packet (RFC 9000 §19.3.1), and no signed overflow occurs |
| `range_intersect` | `ngtcp2_range_intersect` is exact set intersection with a canonical empty range; `ngtcp2_range_cut` computes `a \ b` |
| `ringbuf_model` | For every sequence of 6 push/pop operations at capacity 4, `ngtcp2_ringbuf` refines an abstract bounded deque: `len`, `full()` and `get(i)` match the model, and every slot is in bounds |

## Results

See `results.json` for per-backend times, obligation counts and failures. The
status at the time of the PR is listed in the PR description and updated as
the remaining lemmas finish.

## Limitations

* These are **bounded** proofs. Buffer-based lemmas hold for all inputs up to
  `MAXLEN` bytes, given per lemma in `lemmas.json`. The decoders' checks do
  not depend on the absolute length, so the bound mainly limits how many
  repetitions (e.g. ACK ranges) are explored. It is still a bound.
* Only the listed functions are covered, not the connection state machine
  (`ngtcp2_conn.c`), congestion control or crypto.
* The configuration models a little-endian Linux host (`include/config.h`).
