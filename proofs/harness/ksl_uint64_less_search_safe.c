#include <stdlib.h>
#include "ngtcp2_ksl.h"
/* ksl_uint64_less_search scans a block's keys to find an insertion index.
   It must never read past blk->keys[blk->n) and must return an index in
   [0, blk->n].  8-byte keys. */
void harness(void) {
  size_t n; __CPROVER_assume(n <= NGTCP2_KSL_MAX_NBLK);
  ngtcp2_ksl ksl; ksl.aligned_keylen = 8;
  ngtcp2_ksl_blk blk; blk.n = (uint32_t)n;
  uint8_t *keys = malloc(n ? n * 8 : 1); __CPROVER_assume(keys != NULL);
  blk.keys = keys;
  uint64_t key;
  size_t r = ngtcp2_ksl_uint64_less_search(&ksl, &blk, &key);
  __CPROVER_assert(r <= n, "search index <= n");
  free(keys);
}
