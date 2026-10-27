/* bbr leaf arithmetic helpers: no divide-by-zero / undefined shift.
   - min_pipe_cwnd, bbr_inflight_with_headroom: UB-free for any state
     (const divisor, guarded subtraction).
   - bbr_raise_inflight_longterm_slope: the 1ULL<<bw_probe_up_rounds shift is
     safe under the maintained invariant bw_probe_up_rounds <= 30. */
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
  unsigned which; __CPROVER_assume(which < 2);
  if (which == 0) {
    (void)bbr_inflight_with_headroom(&bbr, &cstat);   /* also calls min_pipe_cwnd */
  } else {
    __CPROVER_assume(bbr.bw_probe_up_rounds <= 30);   /* maintained invariant */
    bbr_raise_inflight_longterm_slope(&bbr, &cstat);
    __CPROVER_assert(bbr.bw_probe_up_rounds <= 30, "rounds stays <= 30");
  }
}
