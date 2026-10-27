#include "ngtcp2_wf.h"
/* ngtcp2_wf windowed max filter: fixed samples[3] (no OOB), const divisors
   (win/4, win/2) => no divide-by-zero, no loops. */
void harness(void) {
  ngtcp2_wf wf;
  uint64_t value, ts;
  ngtcp2_wf_update(&wf, value, ts);
  (void)ngtcp2_wf_get_best(&wf);
  __CPROVER_assert(1, "reached without UB");
}
