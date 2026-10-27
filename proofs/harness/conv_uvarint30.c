#include "ngtcp2_conv.h"
/* Lemma: put_uvarint30 always emits a 4-byte varint that decodes to n
   (used for the Long header Length field, which is pre-reserved). */
void harness(void) {
  uint32_t n; uint8_t buf[4]; uint64_t m;
  __CPROVER_assume(n < (1u << 30));
  __CPROVER_assert(ngtcp2_put_uvarint30(buf, n) == buf + 4, "4 bytes");
  __CPROVER_assert(ngtcp2_get_uvarintlen(buf) == 4, "prefix says 4");
  ngtcp2_get_uvarint(&m, buf);
  __CPROVER_assert(m == n, "roundtrip");
}
