#include <stdlib.h>
#include "ngtcp2_conv.h"
/* Lemma: for ANY byte sequence whose length equals get_uvarintlen(first
   byte), get_uvarint reads only those bytes (no OOB), returns p+len, and
   the decoded value is < 2^62 (fits a QUIC varint). */
void harness(void) {
  uint8_t first;
  size_t len = ngtcp2_get_uvarintlen(&first);
  __CPROVER_assert(len == 1 || len == 2 || len == 4 || len == 8, "len in {1,2,4,8}");
  uint8_t *buf = malloc(len);
  __CPROVER_assume(buf != NULL);
  buf[0] = first;
  uint64_t v;
  const uint8_t *q = ngtcp2_get_uvarint(&v, buf);
  __CPROVER_assert(q == buf + len, "consumes exactly len bytes");
  __CPROVER_assert(v <= NGTCP2_MAX_VARINT, "value fits 62 bits");
  free(buf);
}
