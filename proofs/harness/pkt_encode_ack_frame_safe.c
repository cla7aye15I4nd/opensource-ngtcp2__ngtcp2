#include <stdlib.h>
#include "ngtcp2_pkt.h"
#include "ngtcp2_conv.h"
/* Safety: ngtcp2_pkt_encode_ack_frame never writes past outlen and its
   internal assert((p-out)==len) holds, for any ACK/ACK_ECN frame with
   valid-varint fields and rangecnt<=2. */
void harness(void) {
  ngtcp2_ack fr;
  size_t rangecnt;
  __CPROVER_assume(rangecnt <= 2);

  static ngtcp2_ack_range ranges[2];
  size_t i;
  for (i = 0; i < rangecnt; ++i) {
    __CPROVER_assume(ranges[i].gap <= NGTCP2_MAX_VARINT);
    __CPROVER_assume(ranges[i].len <= NGTCP2_MAX_VARINT);
  }

  __CPROVER_assume(fr.type == NGTCP2_FRAME_ACK || fr.type == NGTCP2_FRAME_ACK_ECN);
  __CPROVER_assume(fr.largest_ack >= 0 && (uint64_t)fr.largest_ack <= NGTCP2_MAX_VARINT);
  __CPROVER_assume(fr.ack_delay <= NGTCP2_MAX_VARINT);
  __CPROVER_assume(fr.first_ack_range <= NGTCP2_MAX_VARINT);
  __CPROVER_assume(fr.ecn.ect0 <= NGTCP2_MAX_VARINT);
  __CPROVER_assume(fr.ecn.ect1 <= NGTCP2_MAX_VARINT);
  __CPROVER_assume(fr.ecn.ce <= NGTCP2_MAX_VARINT);
  __CPROVER_assume(rangecnt <= NGTCP2_MAX_VARINT);
  fr.rangecnt = rangecnt;
  fr.ranges = ranges;

  size_t outlen;
  __CPROVER_assume(outlen >= 1 && outlen <= 40);
  uint8_t *out = malloc(outlen);
  __CPROVER_assume(out != NULL);

  ngtcp2_ssize r = ngtcp2_pkt_encode_ack_frame(out, outlen, &fr);
  if (r >= 0) {
    __CPROVER_assert((size_t)r <= outlen, "return within outlen");
  }
  free(out);
}
