/* Prove reno on-ack path has no divide-by-zero / undefined shift.  cc.c's
   logging uses a _Generic macro CBMC's frontend can't type-check, so we
   include ngtcp2_log.h first (its include guard then neutralizes cc.c's own
   re-include) and replace the log macros with no-ops before compiling cc.c
   into this TU.  Runtime behavior of the arithmetic is unchanged. */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_cc.c"

void harness(void) {
  ngtcp2_cc_reno reno;
  ngtcp2_conn_stat cstat;
  /* Real invariants maintained by the connection: a sane MTU, cwnd floored at
     2*MTU and far below the uint64 range, a sane ssthresh. */
  __CPROVER_assume(cstat.max_tx_udp_payload_size >= 1200 &&
                   cstat.max_tx_udp_payload_size <= 65535);
  __CPROVER_assume(cstat.cwnd >= 2 * cstat.max_tx_udp_payload_size &&
                   cstat.cwnd <= ((uint64_t)1 << 40));
  __CPROVER_assume(cstat.ssthresh <= ((uint64_t)1 << 40));
  ngtcp2_cc_pkt pkt;
  __CPROVER_assume(pkt.pktlen <= cstat.max_tx_udp_payload_size);
  __CPROVER_assume(reno.pending_add < cstat.cwnd);
  ngtcp2_tstamp ts;
  ngtcp2_cc_reno_cc_on_pkt_acked(&reno.cc, &cstat, &pkt, ts);
  __CPROVER_assert(cstat.cwnd >= 1, "cwnd stays >= 1 (no div-by-zero reached)");
}
