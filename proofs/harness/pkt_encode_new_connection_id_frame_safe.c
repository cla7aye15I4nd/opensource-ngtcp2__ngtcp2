#include <stdlib.h>
#include "ngtcp2_pkt.h"
#include "ngtcp2_conv.h"
void harness(void) {
  ngtcp2_new_connection_id fr;
  __CPROVER_assume(fr.seq <= NGTCP2_MAX_VARINT);
  __CPROVER_assume(fr.retire_prior_to <= NGTCP2_MAX_VARINT);
  __CPROVER_assume(fr.cid.datalen <= NGTCP2_MAX_CIDLEN);
  size_t outlen; __CPROVER_assume(outlen >= 1 && outlen <= 48);
  uint8_t *out = malloc(outlen); __CPROVER_assume(out != NULL);
  ngtcp2_ssize r = ngtcp2_pkt_encode_new_connection_id_frame(out, outlen, &fr);
  if (r >= 0) __CPROVER_assert((size_t)r <= outlen, "return within outlen");
  free(out);
}
