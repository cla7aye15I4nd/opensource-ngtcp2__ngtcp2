#include <stdlib.h>
#include "ngtcp2_str.h"
#include <stdint.h>
static size_t naive_hexlen(uint64_t n) { size_t d = 1; while (n >= 16) { n /= 16; ++d; } return d; }
void harness(void) {
  uint64_t n;
  size_t len = ngtcp2_encode_uint_hexlen(n);
  __CPROVER_assert(len == naive_hexlen(n), "hexlen correct");
  uint8_t *buf = malloc(len); __CPROVER_assume(buf != NULL);
  uint8_t *end = ngtcp2_encode_uint_hex(buf, n);
  __CPROVER_assert(end == buf + len, "encode_uint_hex advance == hexlen");
  free(buf);
}
