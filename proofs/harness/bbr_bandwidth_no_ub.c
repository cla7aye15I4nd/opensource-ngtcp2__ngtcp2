/* bbr_update_ack_aggregation / bbr_update_max_bw / bbr_update_round: no
   divide-by-zero or undefined shift. Subtractions are unsigned (defined) and
   the guarded extra computation can't underflow; divisors are constants. */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_bbr.c"

void harness(void) {
  ngtcp2_cc_bbr bbr;
  ngtcp2_rst rst;
  bbr.rst = &rst;
  ngtcp2_conn_stat cstat;
  __CPROVER_assume(cstat.max_tx_udp_payload_size <= 65535);
  ngtcp2_cc_ack ack;
  ngtcp2_tstamp ts;
  unsigned which; __CPROVER_assume(which < 2);
  if (which == 0) bbr_update_ack_aggregation(&bbr, &cstat, &ack, ts);
  else bbr_update_max_bw(&bbr, &cstat, &ack);
  __CPROVER_assert(1, "reached without UB");
}
