#include "ngtcp2_conv.h"
/* Lemma: fixed-width big-endian put/get are inverse and match the
   network-byte-order spec byte by byte. */
void harness(void) {
  uint64_t a; uint32_t b, c; uint16_t d;
  uint8_t buf[8];
  uint64_t a2; uint32_t b2, c2; uint16_t d2;
  ngtcp2_put_uint64be(buf, a);
  for (int i = 0; i < 8; ++i)
    __CPROVER_assert(buf[i] == (uint8_t)(a >> (56 - 8 * i)), "u64 BE byte");
  ngtcp2_get_uint64be(&a2, buf);
  __CPROVER_assert(a2 == a, "u64 roundtrip");
  ngtcp2_put_uint32be(buf, b);
  ngtcp2_get_uint32be(&b2, buf);
  __CPROVER_assert(b2 == b && buf[0] == (uint8_t)(b >> 24), "u32 roundtrip");
  __CPROVER_assume(c < (1u << 24));
  __CPROVER_assert(ngtcp2_put_uint24be(buf, c) == buf + 3, "u24 len");
  ngtcp2_get_uint24be(&c2, buf);
  __CPROVER_assert(c2 == c && buf[0] == (uint8_t)(c >> 16), "u24 roundtrip");
  ngtcp2_put_uint16be(buf, d);
  ngtcp2_get_uint16be(&d2, buf);
  __CPROVER_assert(d2 == d && buf[0] == (uint8_t)(d >> 8), "u16 roundtrip");
}
