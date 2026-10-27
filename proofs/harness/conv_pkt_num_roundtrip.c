#include "ngtcp2_conv.h"
/* Lemma: for len in 1..4, get_pkt_num(put_pkt_num(x, len), len) is x
   truncated to 8*len bits; put writes exactly len bytes, big-endian. */
void harness(void) {
  int64_t x; size_t len; uint8_t buf[4];
  __CPROVER_assume(len >= 1 && len <= 4);
  __CPROVER_assume(x >= 0 && x <= (int64_t)((1ULL << 62) - 1));
  uint8_t *end = ngtcp2_put_pkt_num(buf, x, len);
  __CPROVER_assert(end == buf + len, "writes len bytes");
  uint64_t mask = (1ULL << (8 * len)) - 1;
  __CPROVER_assert((uint64_t)ngtcp2_get_pkt_num(buf, len) == ((uint64_t)x & mask), "roundtrip mod 2^(8len)");
  __CPROVER_assert(buf[len - 1] == (uint8_t)x, "big-endian: last byte is LSB");
}
