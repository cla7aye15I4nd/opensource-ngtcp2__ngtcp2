#include "ngtcp2_conv.h"
/* Lemma: for all n < 2^62, get_uvarint(put_uvarint(n)) == n, the encoded
   length equals put_uvarintlen(n), get_uvarintlen agrees, and the encoding
   is the shortest form defined by RFC 9000 Section 16. */
void harness(void) {
  uint64_t n, m;
  uint8_t buf[8];
  __CPROVER_assume(n < (1ULL << 62));
  uint8_t *end = ngtcp2_put_uvarint(buf, n);
  size_t len = (size_t)(end - buf);
  __CPROVER_assert(len == ngtcp2_put_uvarintlen(n), "length matches put_uvarintlen");
  __CPROVER_assert(len == ngtcp2_get_uvarintlen(buf), "length prefix decodes");
  const uint8_t *q = ngtcp2_get_uvarint(&m, buf);
  __CPROVER_assert(q == end, "decoder consumes exactly encoded bytes");
  __CPROVER_assert(m == n, "roundtrip");
  __CPROVER_assert((len == 1 && n < 64) || (len == 2 && n >= 64 && n < 16384) ||
                   (len == 4 && n >= 16384 && n < (1ULL << 30)) ||
                   (len == 8 && n >= (1ULL << 30)), "minimal encoding");
}
