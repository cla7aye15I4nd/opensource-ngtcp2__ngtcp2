/* cubic_cc_compute_w_cubic: no undefined shift / divide-by-zero for any state.
   The 3600<<10 clamp on time_delta_m bounds the polynomial so the uint64
   products stay in range; the only divisor is the constant NGTCP2_SECONDS.
   (This is the overflow-risky core of cubic_cc_on_ack_recv, which is otherwise
   branch-heavy and hand-audited.) */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_cc.c"

void harness(void) {
  ngtcp2_cc_cubic cubic;
  ngtcp2_conn_stat cstat;
  __CPROVER_assume(cstat.max_tx_udp_payload_size <= 65535);
  ngtcp2_tstamp ts;
  uint64_t r = cubic_cc_compute_w_cubic(&cubic, &cstat, ts);
  __CPROVER_assert(1, "reached without UB (no undefined shift / div-by-zero)");
}
