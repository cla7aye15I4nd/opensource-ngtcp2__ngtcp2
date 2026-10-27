#include <stdlib.h>
#include "ngtcp2_pkt.h"
#include "ngtcp2_conv.h"
void harness(void) {
  ngtcp2_connection_close fr;
  __CPROVER_assume(fr.type == NGTCP2_FRAME_CONNECTION_CLOSE || fr.type == NGTCP2_FRAME_CONNECTION_CLOSE_APP);
  __CPROVER_assume(fr.error_code <= NGTCP2_MAX_VARINT);
  __CPROVER_assume(fr.frame_type <= NGTCP2_MAX_VARINT);
  size_t reasonlen; __CPROVER_assume(reasonlen <= 4);
  static uint8_t reason[4];
  fr.reasonlen = reasonlen; fr.reason = reason;
  size_t outlen; __CPROVER_assume(outlen >= 1 && outlen <= 32);
  uint8_t *out = malloc(outlen); __CPROVER_assume(out != NULL);
  ngtcp2_ssize r = ngtcp2_pkt_encode_connection_close_frame(out, outlen, &fr);
  if (r >= 0) __CPROVER_assert((size_t)r <= outlen, "return within outlen");
  free(out);
}
