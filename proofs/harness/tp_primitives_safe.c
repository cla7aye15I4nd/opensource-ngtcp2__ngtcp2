/* Prove the transport-parameter decode PRIMITIVES (static) are memory-safe on
   untrusted input by compiling them into this translation unit.  These are the
   bounds-checking core that the full ngtcp2_transport_params_decode is built
   from (the monolithic decode's ~20-way switch is too large for CBMC, but it
   performs no raw reads of its own — every byte is consumed through these). */
#include <stdlib.h>
#include "ngtcp2_transport_params.c"

void harness(void) {
  size_t n; __CPROVER_assume(n <= 10);
  uint8_t *buf = malloc(n ? n : 1); __CPROVER_assume(buf != NULL);
  const uint8_t *end = buf + n;

  unsigned which; __CPROVER_assume(which < 4);
  if (which == 0) {
    const uint8_t *p = buf; uint64_t v;
    int r = decode_varint(&v, &p, end);
    if (r == 0) __CPROVER_assert(p > buf && p <= end, "varint advance in (buf,end]");
    else        __CPROVER_assert(p == buf, "varint no advance on fail");
  } else if (which == 1) {
    const uint8_t *p = buf; uint64_t v;
    int r = decode_varint_param(&v, &p, end);
    if (r == 0) __CPROVER_assert(p > buf && p <= end, "varint_param advance in (buf,end]");
  } else if (which == 2) {
    const uint8_t *p = buf; ngtcp2_cid cid;
    int r = decode_cid_param(&cid, &p, end);
    if (r == 0) __CPROVER_assert(p >= buf && p <= end && cid.datalen <= NGTCP2_MAX_CIDLEN,
                                 "cid_param advance in [buf,end], valid cidlen");
  } else {
    const uint8_t *p = buf;
    int r = decode_zero_param(&p, end);
    if (r == 0) __CPROVER_assert(p == buf + 1 && n >= 1, "zero_param consumes 1");
  }
  free(buf);
}
