/* bbr_set_send_quantum (divides by pacing_interval_m, floored at 1 by the
   pacing functions) + bbr_bound_cwnd_for_model / _for_probe_rtt (min/max
   compositions): no divide-by-zero / undefined shift. */
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
  unsigned which; __CPROVER_assume(which < 3);
  if (which == 0) {
    __CPROVER_assume(cstat.pacing_interval_m >= 1);   /* maintained invariant */
    bbr_set_send_quantum(&bbr, &cstat);
  } else if (which == 1) {
    bbr_bound_cwnd_for_model(&bbr, &cstat);
  } else {
    bbr_bound_cwnd_for_probe_rtt(&bbr, &cstat);
  }
  __CPROVER_assert(1, "reached without UB");
}
