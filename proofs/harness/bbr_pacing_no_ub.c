/* bbr pacing-rate functions: no divide-by-zero.
   - init_pacing_rate divides by bbr->initial_cwnd (positive from bbr init).
   - set_pacing_rate_with_gain guards bw==0 and divides by the (nonzero,
     constant) gain argument and the constant (100-margin). */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_bbr.c"

void harness(void) {
  ngtcp2_cc_bbr bbr;
  ngtcp2_conn_stat cstat;
  __CPROVER_assume(bbr.initial_cwnd >= 1);
  unsigned which; __CPROVER_assume(which < 2);
  if (which == 0) {
    bbr_init_pacing_rate(&bbr, &cstat);
  } else {
    uint64_t gain_h; __CPROVER_assume(gain_h >= 1);
    bbr_set_pacing_rate_with_gain(&bbr, &cstat, gain_h);
  }
  __CPROVER_assert(1, "reached without divide-by-zero");
}
