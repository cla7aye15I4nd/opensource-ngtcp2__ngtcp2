/* ngtcp2_dcidtr_verify_cid_uniqueness: scans the bound + unused CID ringbufs
   comparing a new CID (cid_eq full-range datalen safety is proved separately in cid_compare_safe; here CIDs are kept short to isolate the ringbuf-iteration bounds); never reads an entry out of bounds (ringbuf_get(i) for
   i<len; cid_eq bounded by datalen<=NGTCP2_MAX_CIDLEN). */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_dcidtr.c"

void harness(void) {
  ngtcp2_dcidtr dtr;
  ngtcp2_dcidtr_init(&dtr);
  size_t nb, nu;
  __CPROVER_assume(nb <= NGTCP2_DCIDTR_MAX_BOUND_DCID_SIZE);
  __CPROVER_assume(nu <= NGTCP2_DCIDTR_MAX_UNUSED_DCID_SIZE);
  for (size_t i = 0; i < nb; ++i) {
    ngtcp2_dcid *d = ngtcp2_ringbuf_push_back(&dtr.bound.rb);
    __CPROVER_assume(d->cid.datalen <= 4);
  }
  for (size_t i = 0; i < nu; ++i) {
    ngtcp2_dcid *d = ngtcp2_ringbuf_push_back(&dtr.unused.rb);
    __CPROVER_assume(d->cid.datalen <= 4);
  }
  ngtcp2_cid cid;
  __CPROVER_assume(cid.datalen <= 4);
  int r = ngtcp2_dcidtr_verify_cid_uniqueness(&dtr, &cid);
  __CPROVER_assert(r == 0 || r == NGTCP2_ERR_PROTO, "well-defined result");
}
