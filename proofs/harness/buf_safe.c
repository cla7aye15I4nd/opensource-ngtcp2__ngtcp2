#include <stdlib.h>
#include "ngtcp2_buf.h"
/* ngtcp2_buf_init/_cap/_trunc keep pos<=last<=end for any in-bounds state. */
void harness(void) {
  size_t cap; __CPROVER_assume(cap <= 32);
  uint8_t *mem = malloc(cap ? cap : 1); __CPROVER_assume(mem != NULL);
  ngtcp2_buf buf; ngtcp2_buf_init(&buf, mem, cap);
  __CPROVER_assert(ngtcp2_buf_cap(&buf) == cap, "cap == len");
  size_t p, l; __CPROVER_assume(p <= l && l <= cap);
  buf.pos = mem + p; buf.last = mem + l;
  size_t len;
  ngtcp2_buf_trunc(&buf, len);
  __CPROVER_assert(buf.pos <= buf.last, "pos <= last after trunc");
  __CPROVER_assert(buf.last <= buf.end, "last <= end after trunc");
  free(mem);
}
