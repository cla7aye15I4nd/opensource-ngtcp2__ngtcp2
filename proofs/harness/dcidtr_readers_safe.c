/* dcidtr earliest_bound_ts / earliest_retired_ts: no OOB ringbuf access.
   earliest_bound_ts asserts the bound-dcid invariant (cid non-empty, valid
   bound_ts) on each entry, which we establish on the pushed entries. */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_dcidtr.c"

void harness(void) {
  ngtcp2_dcidtr dtr;
  ngtcp2_dcidtr_init(&dtr);
  size_t nb, nr;
  __CPROVER_assume(nb <= NGTCP2_DCIDTR_MAX_BOUND_DCID_SIZE);
  __CPROVER_assume(nr <= NGTCP2_DCIDTR_MAX_RETIRED_DCID_SIZE);
  for (size_t i = 0; i < nb; ++i) {
    ngtcp2_dcid *d = ngtcp2_ringbuf_push_back(&dtr.bound.rb);
    __CPROVER_assume(d->cid.datalen >= 1 && d->cid.datalen <= 4);
    __CPROVER_assume(d->bound_ts != UINT64_MAX);     /* bound-dcid invariant */
  }
  for (size_t i = 0; i < nr; ++i) (void)ngtcp2_ringbuf_push_back(&dtr.retired.rb);
  unsigned which; __CPROVER_assume(which < 2);
  if (which == 0) (void)ngtcp2_dcidtr_earliest_bound_ts(&dtr);
  else (void)ngtcp2_dcidtr_earliest_retired_ts(&dtr);
  __CPROVER_assert(1, "reached without UB");
}
