/* Path-free cid.c/pq.c functions: scid_copy, dcid_set_token (16B token copy),
   cid_empty, pq_empty. (dcid_copy/copy_cid_token copy an embedded path and
   need valid nested addr pointers — the conn-state entanglement, deferred.) */
#include "ngtcp2_cid.h"
#include "ngtcp2_pq.h"
void harness(void) {
  unsigned which; __CPROVER_assume(which < 4);
  if (which == 0) { ngtcp2_scid s, d; __CPROVER_assume(s.cid.datalen <= NGTCP2_MAX_CIDLEN); ngtcp2_scid_copy(&d, &s); }
  else if (which == 1) { ngtcp2_dcid d; ngtcp2_stateless_reset_token t; ngtcp2_dcid_set_token(&d, &t); }
  else if (which == 2) { ngtcp2_cid c; __CPROVER_assume(c.datalen <= NGTCP2_MAX_CIDLEN); (void)ngtcp2_cid_empty(&c); }
  else { ngtcp2_pq pq; pq.length = 0; (void)ngtcp2_pq_empty(&pq); }
  __CPROVER_assert(1, "reached without UB");
}
