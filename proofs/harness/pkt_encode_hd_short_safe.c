#include <stdlib.h>
#include "ngtcp2_pkt.h"
#include "ngtcp2_conv.h"
/* ngtcp2_pkt_encode_hd_short: no write past outlen; internal length invariant. */
void harness(void) {
  ngtcp2_pkt_hd hd;
  __CPROVER_assume(hd.dcid.datalen <= NGTCP2_MAX_CIDLEN);
  __CPROVER_assume(hd.pkt_numlen >= 1 && hd.pkt_numlen <= 4);
  size_t outlen; __CPROVER_assume(outlen >= 1 && outlen <= 40);
  uint8_t *out = malloc(outlen); __CPROVER_assume(out != NULL);
  ngtcp2_ssize r = ngtcp2_pkt_encode_hd_short(out, outlen, &hd);
  if (r >= 0) __CPROVER_assert((size_t)r <= outlen, "return within outlen");
  free(out);
}
