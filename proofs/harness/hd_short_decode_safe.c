#include <stdlib.h>
#include "ngtcp2_pkt.h"
/* Lemma: ngtcp2_pkt_decode_hd_short is memory safe for every input and
   every legal local DCID length, and returns exactly 1 + dcidlen. */
void harness(void) {
  size_t pktlen, dcidlen;
  __CPROVER_assume(pktlen >= 1 && pktlen <= MAXLEN);
  __CPROVER_assume(dcidlen <= NGTCP2_MAX_CIDLEN);
  uint8_t *pkt = malloc(pktlen);
  __CPROVER_assume(pkt != NULL);
  ngtcp2_pkt_hd hd;
  ngtcp2_ssize rv = ngtcp2_pkt_decode_hd_short(&hd, pkt, pktlen, dcidlen);
  if (rv < 0) {
    __CPROVER_assert(pktlen < 1 + dcidlen || (pkt[0] & NGTCP2_HEADER_FORM_BIT), "errors only on short input or long form");
    return;
  }
  __CPROVER_assert((size_t)rv == 1 + dcidlen && hd.dcid.datalen == dcidlen, "length is 1 + dcidlen");
  __CPROVER_assert(hd.type == NGTCP2_PKT_1RTT && hd.tokenlen == 0, "1-RTT without token");
}
