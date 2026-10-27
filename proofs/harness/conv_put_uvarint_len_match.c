#include <stdlib.h>
#include "ngtcp2_conv.h"
/* Foundational lemma for ALL frame encoders: for every valid QUIC varint
   value n (< 2^62), ngtcp2_put_uvarint advances the pointer by EXACTLY
   ngtcp2_put_uvarintlen(n) bytes and writes only within those bytes.
   If this ever failed, every ngtcp2_pkt_encode_*_frame would OOB-write,
   because each precomputes its buffer bound from put_uvarintlen but writes
   with put_uvarint. */
void harness(void) {
  uint64_t n;
  __CPROVER_assume(n <= NGTCP2_MAX_VARINT);
  size_t len = ngtcp2_put_uvarintlen(n);
  __CPROVER_assert(len == 1 || len == 2 || len == 4 || len == 8, "len in {1,2,4,8}");
  uint8_t *buf = malloc(len);            /* exactly len bytes */
  __CPROVER_assume(buf != NULL);
  uint8_t *q = ngtcp2_put_uvarint(buf, n);   /* bounds-check => no OOB write */
  __CPROVER_assert(q == buf + len, "put_uvarint advance == put_uvarintlen");
  free(buf);
}
