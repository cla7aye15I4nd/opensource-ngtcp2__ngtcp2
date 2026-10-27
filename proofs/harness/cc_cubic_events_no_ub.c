/* cubic on_spurious_congestion / on_persistent_congestion / reset: no
   div-by-zero / UB.  reset->init_pacing_rate needs the current cwnd>=1; the
   restore path sets cwnd=undo.cwnd (>cwnd>=1). Logging neutralized. */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_cc.c"

void harness(void) {
  ngtcp2_cc_cubic cubic;
  ngtcp2_conn_stat cstat;
  __CPROVER_assume(cstat.max_tx_udp_payload_size >= 1200 &&
                   cstat.max_tx_udp_payload_size <= 65535);
  __CPROVER_assume(cstat.cwnd >= 2 * cstat.max_tx_udp_payload_size &&
                   cstat.cwnd <= ((uint64_t)1 << 40));
  ngtcp2_tstamp ts;
  unsigned which; __CPROVER_assume(which < 3);
  if (which == 0) ngtcp2_cc_cubic_cc_on_spurious_congestion(&cubic.cc, &cstat, ts);
  else if (which == 1) ngtcp2_cc_cubic_cc_on_persistent_congestion(&cubic.cc, &cstat, ts);
  else ngtcp2_cc_cubic_cc_reset(&cubic.cc, &cstat, ts);
  __CPROVER_assert(cstat.cwnd >= 1, "cwnd >= 1 after cubic event");
}
