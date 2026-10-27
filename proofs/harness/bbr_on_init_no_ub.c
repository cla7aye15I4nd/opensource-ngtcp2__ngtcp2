/* bbr_on_init: sets bbr fields and calls the already-proved reset/enter/init
   helpers.  No divide-by-zero / undefined shift under init invariants. */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_bbr.c"
#include "ngtcp2_pcg.h"

void harness(void) {
  ngtcp2_cc_bbr bbr;
  ngtcp2_rst rst; bbr.rst = &rst;
  ngtcp2_pcg32 pcg; bbr.pcg = &pcg;
  ngtcp2_conn_stat cstat;
  __CPROVER_assume(cstat.max_tx_udp_payload_size >= 1200 &&
                   cstat.max_tx_udp_payload_size <= 65535);
  __CPROVER_assume(bbr.initial_cwnd >= 1);
  ngtcp2_tstamp initial_ts;
  bbr_on_init(&bbr, &cstat, initial_ts);
  __CPROVER_assert(1, "reached without UB");
}
