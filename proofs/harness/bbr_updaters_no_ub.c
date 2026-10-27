/* bbr updater functions (compositions of already-proved helpers + assignments):
   no divide-by-zero / undefined shift. */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_bbr.c"

void harness(void) {
  ngtcp2_cc_bbr bbr;
  ngtcp2_conn_stat cstat;
  __CPROVER_assume(cstat.max_tx_udp_payload_size <= 65535);
  unsigned which; __CPROVER_assume(which < 5);
  if (which == 0) bbr_update_max_inflight(&bbr, &cstat);
  else if (which == 1) bbr_update_offload_budget(&bbr, &cstat);
  else if (which == 2) bbr_save_cwnd(&bbr, &cstat);
  else if (which == 3) bbr_advance_max_bw_filter(&bbr);
  else bbr_restore_cwnd(&bbr, &cstat);
  __CPROVER_assert(1, "reached without UB");
}
