#include <stdlib.h>
#include "ngtcp2_ksl.h"
#include "ngtcp2_range.h"
/* ksl_range_search: 16-byte range keys; no OOB key read, index in [0,n]. */
void harness(void) {
  size_t n; __CPROVER_assume(n <= NGTCP2_KSL_MAX_NBLK);
  ngtcp2_ksl ksl; ksl.aligned_keylen = 16;
  ngtcp2_ksl_blk blk; blk.n = (uint32_t)n;
  uint8_t *keys = malloc(n ? n * 16 : 1); __CPROVER_assume(keys != NULL);
  blk.keys = keys;
  ngtcp2_range key;
  size_t r = ngtcp2_ksl_range_search(&ksl, &blk, &key);
  __CPROVER_assert(r <= n, "search index <= n");
  free(keys);
}
