#include "ngtcp2_cid.h"
/* ngtcp2_cid_eq / ngtcp2_cid_less: memory-safe over valid CIDs and form a
   consistent order (eq reflexive+symmetric, less irreflexive, eq => not less). */
void harness(void) {
  ngtcp2_cid a, b;
  __CPROVER_assume(a.datalen <= NGTCP2_MAX_CIDLEN);
  __CPROVER_assume(b.datalen <= NGTCP2_MAX_CIDLEN);
  __CPROVER_assert(ngtcp2_cid_eq(&a, &a) == 1, "cid_eq reflexive");
  __CPROVER_assert(ngtcp2_cid_eq(&a, &b) == ngtcp2_cid_eq(&b, &a), "cid_eq symmetric");
  __CPROVER_assert(ngtcp2_cid_less(&a, &a) == 0, "cid_less irreflexive");
  if (ngtcp2_cid_eq(&a, &b)) {
    __CPROVER_assert(!ngtcp2_cid_less(&a, &b) && !ngtcp2_cid_less(&b, &a), "eq => not less");
  }
}
