/* bbr reset/init/enter state functions (mostly field assignments; enter_*
   call the already-proved pacing helpers): no divide-by-zero / undefined
   shift. */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_bbr.c"

void harness(void) {
  ngtcp2_cc_bbr bbr;
  ngtcp2_rst rst; bbr.rst = &rst;
  ngtcp2_conn_stat cstat;
  __CPROVER_assume(bbr.initial_cwnd >= 1);
  unsigned which; __CPROVER_assume(which < 8);
  switch (which) {
  case 0: bbr_reset_congestion_signals(&bbr); break;
  case 1: bbr_reset_shortterm_model(&bbr); break;
  case 2: bbr_reset_full_bw(&bbr); break;
  case 3: bbr_init_round_counting(&bbr); break;
  case 4: bbr_init_lower_bounds(&bbr, &cstat); break;
  case 5: bbr_enter_startup(&bbr); break;
  case 6: bbr_enter_drain(&bbr); break;
  default: bbr_start_round(&bbr); break;
  }
  __CPROVER_assert(1, "reached without UB");
}
