#include <stdlib.h>
#include "ngtcp2_pkt.h"
#include "ngtcp2_conv.h"
/* ngtcp2_pkt_encode_hd_long: no write past outlen; internal length invariant
   holds, for any long header with valid CID lengths, pkt_numlen in 1..4,
   hd->len < 2^30 (put_uvarint30 precondition), and small token. */
void harness(void) {
  ngtcp2_pkt_hd hd;
  __CPROVER_assume(hd.dcid.datalen <= NGTCP2_MAX_CIDLEN);
  __CPROVER_assume(hd.scid.datalen <= NGTCP2_MAX_CIDLEN);
  __CPROVER_assume(hd.pkt_numlen >= 1 && hd.pkt_numlen <= 4);
  __CPROVER_assume(hd.len < 1073741824u);
  __CPROVER_assume(hd.type == NGTCP2_PKT_INITIAL || hd.type == NGTCP2_PKT_0RTT ||
                   hd.type == NGTCP2_PKT_HANDSHAKE || hd.type == NGTCP2_PKT_RETRY);
  hd.version = NGTCP2_PROTO_VER_V1;
  size_t tokenlen; __CPROVER_assume(tokenlen <= 4);
  static uint8_t tok[4];
  hd.token = tok; hd.tokenlen = tokenlen;
  size_t outlen; __CPROVER_assume(outlen >= 1 && outlen <= 80);
  uint8_t *out = malloc(outlen); __CPROVER_assume(out != NULL);
  ngtcp2_ssize r = ngtcp2_pkt_encode_hd_long(out, outlen, &hd);
  if (r >= 0) __CPROVER_assert((size_t)r <= outlen, "return within outlen");
  free(out);
}
