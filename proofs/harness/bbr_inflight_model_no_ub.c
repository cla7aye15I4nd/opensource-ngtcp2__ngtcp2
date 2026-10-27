/* bbr inflight-model composition: quantization_budget / inflight /
   target_inflight / probe_rtt_cwnd — all max/min/add over bbr_bdp_multiple
   (already proved div-safe). No new divisors. */
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
  uint64_t gain_h, inflight;
  unsigned which; __CPROVER_assume(which < 4);
  if (which == 0) (void)bbr_quantization_budget(&bbr, &cstat, inflight);
  else if (which == 1) (void)bbr_inflight(&bbr, &cstat, gain_h);
  else if (which == 2) (void)bbr_target_inflight(&bbr, &cstat);
  else (void)bbr_probe_rtt_cwnd(&bbr, &cstat);
  __CPROVER_assert(1, "reached without UB");
}
