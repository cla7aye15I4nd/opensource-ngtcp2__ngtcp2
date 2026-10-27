#include <stdlib.h>
#include "ngtcp2_pkt.h"
/* Lemma: ngtcp2_pkt_decode_version_cid never reads out of bounds and,
   whenever it reports CIDs (rv == 0 or VERSION_NEGOTIATION), both CIDs
   lie inside the datagram.  MAXLEN >= NGTCP2_MAX_UDP_PAYLOAD_SIZE so the
   "unsupported version, long CID" path is covered. */
void harness(void) {
  size_t datalen, short_dcidlen;
  __CPROVER_assume(datalen >= 1 && datalen <= MAXLEN);
  __CPROVER_assume(short_dcidlen <= NGTCP2_MAX_CIDLEN);
  uint8_t *data = malloc(datalen);
  __CPROVER_assume(data != NULL);
  ngtcp2_version_cid vc;
  int rv = ngtcp2_pkt_decode_version_cid(&vc, data, datalen, short_dcidlen);
  if (rv != 0 && rv != NGTCP2_ERR_VERSION_NEGOTIATION) return;
  __CPROVER_assert(vc.dcid >= data && vc.dcid + vc.dcidlen <= data + datalen, "dcid in bounds");
  __CPROVER_assert(vc.scidlen == 0 || (vc.scid >= data && vc.scid + vc.scidlen <= data + datalen), "scid in bounds");
}
