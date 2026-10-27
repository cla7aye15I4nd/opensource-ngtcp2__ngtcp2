#include <stdlib.h>
#include "ngtcp2_pkt.h"
#include "ngtcp2_conv.h"
void harness(void) {
  ngtcp2_new_token fr;
  size_t tokenlen; __CPROVER_assume(tokenlen >= 1 && tokenlen <= 6);
  static uint8_t tok[6];
  fr.token = tok; fr.tokenlen = tokenlen;
  size_t outlen; __CPROVER_assume(outlen >= 1 && outlen <= 16);
  uint8_t *out = malloc(outlen); __CPROVER_assume(out != NULL);
  ngtcp2_ssize r = ngtcp2_pkt_encode_new_token_frame(out, outlen, &fr);
  if (r >= 0) __CPROVER_assert((size_t)r <= outlen, "return within outlen");
  free(out);
}
