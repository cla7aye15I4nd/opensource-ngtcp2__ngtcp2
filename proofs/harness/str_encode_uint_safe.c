#include <stdlib.h>
#include "ngtcp2_str.h"
void harness(void) {
  uint64_t n;
  size_t len = ngtcp2_encode_uintlen(n);
  uint8_t *buf = malloc(len); __CPROVER_assume(buf != NULL);
  uint8_t *end = ngtcp2_encode_uint(buf, n);
  __CPROVER_assert(end == buf + len, "encode_uint advance == encode_uintlen");
  free(buf);
}
