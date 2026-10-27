/* ngtcp2_balloc_get: the bump-pointer pool allocator never writes past the
   block.  Safety rests on blklen being 16-aligned (init assert) + n<=blklen,
   which keeps buf_left 16-aligned so the rounded bump (n+15)&~15 never exceeds
   it.  malloc modelled by CBMC. */
#include <stdlib.h>
#include "ngtcp2_balloc.h"
#include "ngtcp2_mem.h"

void harness(void) {
  const ngtcp2_mem *mem = ngtcp2_mem_default();
  ngtcp2_balloc balloc;
  size_t blklen;
  __CPROVER_assume(blklen >= 16 && blklen <= 256 && (blklen & 0xFU) == 0);
  ngtcp2_balloc_init(&balloc, blklen, mem);
  for (int k = 0; k < 2; ++k) {
    void *buf; size_t n;
    __CPROVER_assume(n <= blklen);
    (void)ngtcp2_balloc_get(&balloc, &buf, n);
  }
  ngtcp2_balloc_free(&balloc);
  __CPROVER_assert(1, "reached without UB");
}
