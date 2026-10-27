/* bbr orchestrators + loss-recovery path: update_on_ack / update_model_and_state
   / handle_inflight_too_high / handle_lost_packet. No divide-by-zero /
   undefined shift under the full maintained invariant set, incl. recovery
   accounting (pkt.tx_in_flight>=pkt.pktlen, rst.lost>=pkt.lost+pkt.pktlen). */
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
  __CPROVER_assume(bbr.probe_up_acked_per_inc >= 1);
  __CPROVER_assume(bbr.pacing_gain_h >= 1);
  ngtcp2_conn_stat cstat;
  __CPROVER_assume(cstat.max_tx_udp_payload_size >= 1200 &&
                   cstat.max_tx_udp_payload_size <= 65535);
  __CPROVER_assume(cstat.cwnd >= 2 * cstat.max_tx_udp_payload_size);
  __CPROVER_assume(cstat.pacing_interval_m >= 1);
  __CPROVER_assume(bbr.initial_cwnd >= 1);
  ngtcp2_cc_ack ack;
  ngtcp2_cc_pkt pkt;
  __CPROVER_assume(pkt.pktlen <= 65535);
  __CPROVER_assume(pkt.tx_in_flight >= pkt.pktlen);
  __CPROVER_assume(rst.lost >= pkt.lost);
  __CPROVER_assume(rst.lost - pkt.lost >= pkt.pktlen);  /* rs.lost >= pktlen, no wrap */
  ngtcp2_rs rs;
  ngtcp2_tstamp ts;
  unsigned which; __CPROVER_assume(which < 4);
  switch (which) {
  case 0: bbr_update_on_ack(&bbr, &cstat, &ack, ts); break;
  case 1: bbr_update_model_and_state(&bbr, &cstat, &ack, ts); break;
  case 2: bbr_handle_inflight_too_high(&bbr, &cstat, &rs, ts); break;
  default: bbr_handle_lost_packet(&bbr, &cstat, &pkt, ts); break;
  }
  __CPROVER_assert(1, "reached without UB");
}
