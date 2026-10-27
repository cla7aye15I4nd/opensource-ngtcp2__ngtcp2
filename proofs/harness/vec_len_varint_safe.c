#include <stdlib.h>
#include "ngtcp2_vec.h"
#include "ngtcp2_conv.h"
/* ngtcp2_vec_len_varint: no OOB read; result is -1 or a valid varint value. */
void harness(void) {
  size_t n; __CPROVER_assume(n <= 3);
  ngtcp2_vec *v = malloc(sizeof(ngtcp2_vec) * (n ? n : 1));
  __CPROVER_assume(v != NULL);
  int64_t r = ngtcp2_vec_len_varint(v, n);
  __CPROVER_assert(r == -1 || (r >= 0 && (uint64_t)r <= NGTCP2_MAX_VARINT),
                   "result is -1 or a 62-bit value");
  free(v);
}
