#include "ngtcp2_rst.h"
#include "ngtcp2_rtb.h"
#include "ngtcp2_conn_stat.h"
/* ngtcp2_rst_on_ack_recv performs a division by rs->interval; prove it is
   never a divide-by-zero (guarded by the !rs->interval early return) and the
   function has no other UB. */
void harness(void) {
  ngtcp2_rst rst;
  ngtcp2_conn_stat cstat;
  ngtcp2_rst_on_ack_recv(&rst, &cstat);
  __CPROVER_assert(1, "reached without UB");
}
