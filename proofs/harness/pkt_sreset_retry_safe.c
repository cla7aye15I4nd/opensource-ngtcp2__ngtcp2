/* ngtcp2_pkt_decode_stateless_reset (untrusted input: reads rand + 16B token
   within payload after the length check) and ngtcp2_pkt_encode_pseudo_retry
   (writes odcid + long header + token within destlen). No OOB. */
#include <stdlib.h>
#include "ngtcp2_pkt.h"
#include <ngtcp2/ngtcp2.h>

void harness(void) {
  unsigned which; __CPROVER_assume(which < 2);
  if (which == 0) {
    size_t payloadlen; __CPROVER_assume(payloadlen <= 40);
    uint8_t *payload = malloc(payloadlen ? payloadlen : 1);
    __CPROVER_assume(payload != NULL);
    ngtcp2_pkt_stateless_reset2 sr;
    int r = ngtcp2_pkt_decode_stateless_reset(&sr, payload, payloadlen);
    __CPROVER_assert(r == 0 || r == NGTCP2_ERR_INVALID_ARGUMENT, "well-defined");
    free(payload);
  } else {
    ngtcp2_pkt_hd hd;
    __CPROVER_assume(hd.dcid.datalen <= NGTCP2_MAX_CIDLEN);
    __CPROVER_assume(hd.scid.datalen <= NGTCP2_MAX_CIDLEN);
    __CPROVER_assume(hd.pkt_numlen >= 1 && hd.pkt_numlen <= 4);
    hd.type = NGTCP2_PKT_RETRY; hd.version = NGTCP2_PROTO_VER_V1;
    ngtcp2_cid odcid; __CPROVER_assume(odcid.datalen <= NGTCP2_MAX_CIDLEN);
    size_t tokenlen; __CPROVER_assume(tokenlen <= 8);
    static uint8_t tok[8];
    size_t destlen; __CPROVER_assume(destlen <= 120);
    uint8_t *dest = malloc(destlen ? destlen : 1); __CPROVER_assume(dest != NULL);
    ngtcp2_ssize r = ngtcp2_pkt_encode_pseudo_retry(dest, destlen, &hd, 0, &odcid, tok, tokenlen);
    if (r >= 0) __CPROVER_assert((size_t)r <= destlen, "within destlen");
    free(dest);
  }
}
