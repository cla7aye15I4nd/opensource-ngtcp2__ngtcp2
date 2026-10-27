/* dcidtr length/full/empty getters: trivial ringbuf_len wrappers, no UB. */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_dcidtr.c"
void harness(void) {
  ngtcp2_dcidtr dtr;
  ngtcp2_dcidtr_init(&dtr);
  (void)ngtcp2_dcidtr_unused_len(&dtr);
  (void)ngtcp2_dcidtr_bound_len(&dtr);
  (void)ngtcp2_dcidtr_retired_len(&dtr);
  (void)ngtcp2_dcidtr_inactive_len(&dtr);
  (void)ngtcp2_dcidtr_unused_full(&dtr);
  (void)ngtcp2_dcidtr_unused_empty(&dtr);
  __CPROVER_assert(1, "reached without UB");
}
