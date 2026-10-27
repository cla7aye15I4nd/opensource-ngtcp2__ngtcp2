/* Container constructors/getters: cid_init (memcpy bounded by datalen<=MAX_CIDLEN),
   scid_init, vec_len (sum, no OOB read), vec_copy. No UB. */
#include <stdlib.h>
#include "ngtcp2_cid.h"
#include "ngtcp2_vec.h"
void harness(void) {
  unsigned which; __CPROVER_assume(which < 4);
  if (which == 0) {
    ngtcp2_cid cid; size_t dl; __CPROVER_assume(dl <= NGTCP2_MAX_CIDLEN);
    uint8_t *data = malloc(dl ? dl : 1); __CPROVER_assume(data != NULL);
    ngtcp2_cid_init(&cid, data, dl); free(data);
  } else if (which == 1) {
    ngtcp2_cid cid; __CPROVER_assume(cid.datalen <= NGTCP2_MAX_CIDLEN);
    ngtcp2_scid scid; uint64_t seq; ngtcp2_scid_init(&scid, seq, &cid);
  } else if (which == 2) {
    size_t n; __CPROVER_assume(n <= 4);
    ngtcp2_vec *v = malloc(sizeof(ngtcp2_vec) * (n ? n : 1)); __CPROVER_assume(v != NULL);
    (void)ngtcp2_vec_len(v, n); free(v);
  } else {
    size_t cnt; __CPROVER_assume(cnt <= 4);
    ngtcp2_vec *dst = malloc(sizeof(ngtcp2_vec) * (cnt ? cnt : 1));
    ngtcp2_vec *src = malloc(sizeof(ngtcp2_vec) * (cnt ? cnt : 1));
    __CPROVER_assume(dst != NULL && src != NULL);
    ngtcp2_vec_copy(dst, src, cnt); free(dst); free(src);
  }
  __CPROVER_assert(1, "reached without UB");
}
