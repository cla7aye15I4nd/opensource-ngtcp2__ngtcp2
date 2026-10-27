/* bbr loss-handling + probe-rtt functions: no divide-by-zero / undefined
   shift under maintained invariants. */
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
  __CPROVER_assume(bbr.bw_probe_up_rounds <= 30);
  ngtcp2_conn_stat cstat;
  __CPROVER_assume(cstat.max_tx_udp_payload_size <= 65535);
  ngtcp2_tstamp ts;
  ngtcp2_cc_ack ack;
  ngtcp2_cc_pkt pkt;
  ngtcp2_rs rs;
  unsigned which; __CPROVER_assume(which < 12);
  switch (which) {
  case 0: bbr_note_loss(&bbr, &cstat); break;
  case 1: bbr_save_state_upon_loss(&bbr, &cstat); break;
  case 2:
    __CPROVER_assume(rs.tx_in_flight >= pkt.pktlen);  /* caller precondition */
    __CPROVER_assume(rs.lost >= pkt.pktlen);
    (void)bbr_inflight_at_loss(&bbr, &pkt, &rs); break;
  case 3: (void)bbr_is_inflight_too_high(&bbr, &rs); break;
  case 4: bbr_update_min_rtt(&bbr, &ack, ts); break;
  case 5: bbr_check_probe_rtt(&bbr, &cstat, ts); break;
  case 6: bbr_enter_probe_rtt(&bbr); break;
  case 7: bbr_check_probe_rtt_done(&bbr, &cstat, ts); break;
  case 8: bbr_exit_probe_rtt(&bbr, ts); break;
  case 9: bbr_mark_connection_app_limited(&bbr, &cstat); break;
  case 10: bbr_handle_restart_from_idle(&bbr, &cstat, ts); break;
  default: bbr_handle_spurious_loss_detection(&bbr, &cstat); break;
  }
  __CPROVER_assert(1, "reached without UB");
}
