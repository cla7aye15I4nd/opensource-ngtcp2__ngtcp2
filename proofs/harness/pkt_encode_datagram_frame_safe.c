#include <stdlib.h>
#include "ngtcp2_pkt.h"
#include "ngtcp2_conv.h"
void harness(void) {
  ngtcp2_datagram fr;
  size_t datacnt; __CPROVER_assume(datacnt <= 2);
  static ngtcp2_vec vecs[2];
  static uint8_t srcbuf[6];
  size_t used = 0, i;
  for (i = 0; i < datacnt; ++i) {
    size_t l; __CPROVER_assume(l <= 3);
    __CPROVER_assume(used + l <= sizeof(srcbuf));
    vecs[i].base = srcbuf + used; vecs[i].len = l; used += l;
  }
  __CPROVER_assume(fr.type == NGTCP2_FRAME_DATAGRAM || fr.type == NGTCP2_FRAME_DATAGRAM_LEN);
  fr.datacnt = datacnt; fr.data = vecs;
  size_t outlen; __CPROVER_assume(outlen >= 1 && outlen <= 32);
  uint8_t *out = malloc(outlen); __CPROVER_assume(out != NULL);
  ngtcp2_ssize r = ngtcp2_pkt_encode_datagram_frame(out, outlen, &fr);
  if (r >= 0) __CPROVER_assert((size_t)r <= outlen, "return within outlen");
  free(out);
}
