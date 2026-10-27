/* bbr_bdp_multiple: no divide-by-zero.  The division by bbr->min_rtt is
   guarded by the short-circuit `bbr->min_rtt && ...`; min_rtt==UINT64_MAX
   returns early; all other divisors (NGTCP2_SECONDS, 100) are nonzero
   constants. */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_bbr.c"

void harness(void) {
  ngtcp2_cc_bbr bbr;
  uint64_t gain_h;
  (void)bbr_bdp_multiple(&bbr, gain_h);
  __CPROVER_assert(1, "reached without divide-by-zero");
}
