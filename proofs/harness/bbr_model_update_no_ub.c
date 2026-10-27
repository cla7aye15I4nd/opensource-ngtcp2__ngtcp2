/* bbr model/control/signal update functions + loss/longterm handlers:
   no divide-by-zero / undefined shift under maintained invariants. */
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
  __CPROVER_assume(cstat.max_tx_udp_payload_size >= 1200 &&
                   cstat.max_tx_udp_payload_size <= 65535);
  __CPROVER_assume(bbr.probe_up_acked_per_inc >= 1);  /* set to max(.,mtu) */
  __CPROVER_assume(bbr.pacing_gain_h >= 1);           /* init constant */
  __CPROVER_assume(cstat.pacing_interval_m >= 1);     /* floored at 1 */
  ngtcp2_cc_ack ack;
  ngtcp2_cc_pkt pkt;
  ngtcp2_rs rs;
  __CPROVER_assume(rs.tx_in_flight >= pkt.pktlen);
  __CPROVER_assume(rs.lost >= pkt.pktlen);
  __CPROVER_assume(rst.rs.tx_in_flight >= pkt.pktlen);  /* recovery accounting */
  __CPROVER_assume(rst.rs.lost >= pkt.pktlen);
  __CPROVER_assume(rst.lost >= pkt.lost);
  ngtcp2_tstamp ts;
  unsigned which; __CPROVER_assume(which < 10);
  switch (which) {
  case 0: bbr_update_latest_delivery_signals(&bbr, &cstat); break;
  case 1: bbr_advance_latest_delivery_signals(&bbr, &cstat); break;
  case 2: bbr_update_congestion_signals(&bbr, &cstat, &ack); break;
  case 3: bbr_update_control_parameters(&bbr, &cstat, &ack); break;
  case 4: bbr_bound_bw_for_model(&bbr); break;
  case 5: bbr_loss_lower_bounds(&bbr); break;
  case 6: (void)bbr_adapt_longterm_model(&bbr, &cstat, &ack); break;
  case 7: bbr_probe_inflight_longterm_upward(&bbr, &cstat, &ack); break;
  case 8: bbr_update_probe_bw_cycle_phase(&bbr, &cstat, &ack, ts); break;
  default: bbr_on_transmit(&bbr, &cstat, ts); break;  /* case 9 */
  }
  __CPROVER_assert(1, "reached without UB");
}
