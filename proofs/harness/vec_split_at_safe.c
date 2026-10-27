#include <stdlib.h>
#include "ngtcp2_vec.h"
/* ngtcp2_vec_split_at: with its precondition offset < src->len, splits
   without OOB and preserves total length (dst.len + src.len == old len). */
void harness(void) {
  ngtcp2_vec src, dst;
  size_t len; __CPROVER_assume(len >= 1 && len <= 8);
  size_t offset; __CPROVER_assume(offset < len);
  uint8_t *buf = malloc(len); __CPROVER_assume(buf != NULL);
  src.base = buf; src.len = len;
  ngtcp2_vec_split_at(&dst, &src, offset);
  __CPROVER_assert(src.len + dst.len == len, "length conserved");
  __CPROVER_assert(dst.base == buf + offset, "dst points past offset");
  free(buf);
}
