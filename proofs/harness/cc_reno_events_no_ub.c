/* reno congestion_event / on_persistent_congestion / reset: no div-by-zero or
   undefined shift.  Each sets cwnd to 2*MTU (>=1) before pacing. Logging
   neutralized via the include technique (see cc_reno_on_acked_no_ub). */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_cc.c"

void harness(void) {
  ngtcp2_cc_reno reno;
  ngtcp2_conn_stat cstat;
  __CPROVER_assume(cstat.max_tx_udp_payload_size >= 1200 &&
                   cstat.max_tx_udp_payload_size <= 65535);
  __CPROVER_assume(cstat.cwnd >= 2 * cstat.max_tx_udp_payload_size &&
                   cstat.cwnd <= ((uint64_t)1 << 40));
  ngtcp2_tstamp ts;
  unsigned which; __CPROVER_assume(which < 3);
  if (which == 0) {
    ngtcp2_cc_ack ack; ngtcp2_tstamp sent_ts;
    ngtcp2_cc_reno_cc_congestion_event(&reno.cc, &cstat, sent_ts, &ack, ts);
  } else if (which == 1) {
    ngtcp2_cc_reno_cc_on_persistent_congestion(&reno.cc, &cstat, ts);
  } else {
    ngtcp2_cc_reno_cc_reset(&reno.cc, &cstat, ts);
  }
  __CPROVER_assert(cstat.cwnd >= 1, "cwnd >= 1 after event");
}
