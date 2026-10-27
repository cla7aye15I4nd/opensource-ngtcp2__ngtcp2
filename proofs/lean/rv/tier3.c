#include "prelude.h"
int ngtcp2_range_not_after(const ngtcp2_range *a, const ngtcp2_range *b) {
  return a->end <= b->end;
}
const uint8_t *ngtcp2_get_uint64be(uint64_t *dest, const uint8_t *p) {
  uint64_t n;
  memcpy(&n, p, 8);
  *dest = ngtcp2_ntohl64(n);
  return p + 8;
}
