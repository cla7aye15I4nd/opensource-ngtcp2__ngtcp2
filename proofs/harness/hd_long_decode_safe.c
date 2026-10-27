#include <stdlib.h>
#include "ngtcp2_pkt.h"
/* Lemma: for every adversarial datagram prefix of length <= MAXLEN,
   ngtcp2_pkt_decode_hd_long has no OOB read/UB/assert failure, returns an
   error or a header length <= pktlen, and on success the CIDs are at most
   NGTCP2_MAX_CIDLEN bytes and the token lies inside the header. */
void harness(void) {
  size_t pktlen;
  __CPROVER_assume(pktlen >= 1 && pktlen <= MAXLEN);
  uint8_t *pkt = malloc(pktlen);
  __CPROVER_assume(pkt != NULL);
  ngtcp2_pkt_hd hd;
  ngtcp2_ssize rv = ngtcp2_pkt_decode_hd_long(&hd, pkt, pktlen);
  if (rv < 0) {
    __CPROVER_assert(rv == NGTCP2_ERR_INVALID_ARGUMENT, "only INVALID_ARGUMENT");
    return;
  }
  __CPROVER_assert(rv >= 7 && (size_t)rv <= pktlen, "header length within packet");
  __CPROVER_assert(hd.dcid.datalen <= NGTCP2_MAX_CIDLEN && hd.scid.datalen <= NGTCP2_MAX_CIDLEN, "CID lengths bounded");
  __CPROVER_assert(hd.tokenlen == 0 || (hd.token >= pkt && hd.token + hd.tokenlen <= pkt + rv), "token in header");
  __CPROVER_assert(hd.tokenlen == 0 || hd.type == NGTCP2_PKT_INITIAL, "only Initial carries a token");
}
