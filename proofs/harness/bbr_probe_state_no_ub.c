/* bbr probe-bw state predicates + transitions: no divide-by-zero / undefined
   shift.  Predicates are field comparisons; transitions set state + call the
   already-proved pacing/inflight helpers. */
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
  __CPROVER_assume(cstat.max_tx_udp_payload_size <= 65535);
  __CPROVER_assume(bbr.bw_probe_up_rounds <= 30);  /* maintained invariant */
  ngtcp2_tstamp ts; ngtcp2_duration interval;
  unsigned which; __CPROVER_assume(which < 12);
  switch (which) {
  case 0: (void)bbr_is_in_probe_bw_state(&bbr); break;
  case 1: (void)bbr_is_probing_bw(&bbr); break;
  case 2: (void)bbr_is_time_to_cruise(&bbr, &cstat); break;
  case 3: (void)bbr_is_time_to_go_down(&bbr, &cstat); break;
  case 4: (void)bbr_has_elapsed_in_phase(&bbr, interval, ts); break;
  case 5: bbr_check_startup_done(&bbr); break;
  case 6: bbr_check_drain_done(&bbr, &cstat, ts); break;
  case 7: bbr_start_probe_bw_down(&bbr, ts); break;
  case 8: bbr_start_probe_bw_cruise(&bbr); break;
  case 9: bbr_start_probe_bw_refill(&bbr); break;
  case 10: bbr_start_probe_bw_up(&bbr, &cstat); break;
  default: bbr_enter_probe_bw(&bbr, ts); break;
  }
  __CPROVER_assert(1, "reached without UB");
}
