#include <stdlib.h>
#include "ngtcp2_vec.h"
/* ngtcp2_vec_copy_at_most: never writes past dst[dstcnt) nor reads past
   src[srccnt); returns at most dstcnt. */
void harness(void) {
  size_t dstcnt, srccnt, left;
  __CPROVER_assume(dstcnt <= 3 && srccnt <= 3);
  ngtcp2_vec *dst = malloc(sizeof(ngtcp2_vec) * (dstcnt ? dstcnt : 1));
  ngtcp2_vec *src = malloc(sizeof(ngtcp2_vec) * (srccnt ? srccnt : 1));
  __CPROVER_assume(dst != NULL && src != NULL);
  size_t r = ngtcp2_vec_copy_at_most(dst, dstcnt, src, srccnt, left);
  __CPROVER_assert(r <= dstcnt, "return <= dstcnt");
  free(dst); free(src);
}
