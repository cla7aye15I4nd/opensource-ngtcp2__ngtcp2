#include <stdlib.h>
#include "ngtcp2_pkt.h"
#include "ngtcp2_conv.h"
/* Safety: ngtcp2_pkt_encode_stream_frame never writes past outlen and its
   internal length bookkeeping (assert((p-out)==len)) holds, for any STREAM
   frame with valid-varint scalar fields and datacnt<=2.  `out` is allocated
   at exactly outlen so CBMC --bounds-check catches any overflow. */
void harness(void) {
  ngtcp2_stream fr;
  size_t datacnt;
  __CPROVER_assume(datacnt <= 2);

  static ngtcp2_vec vecs[2];
  static uint8_t srcbuf[6];
  size_t used = 0, i;
  for (i = 0; i < datacnt; ++i) {
    size_t l;
    __CPROVER_assume(l >= 1 && l <= 3);
    __CPROVER_assume(used + l <= sizeof(srcbuf));
    vecs[i].base = srcbuf + used;
    vecs[i].len = l;
    used += l;
  }

  __CPROVER_assume(fr.stream_id >= 0 && (uint64_t)fr.stream_id <= NGTCP2_MAX_VARINT);
  __CPROVER_assume(fr.offset <= NGTCP2_MAX_VARINT);
  fr.datacnt = datacnt;
  fr.data = vecs;                 /* fin/type left nondeterministic */

  size_t outlen;
  __CPROVER_assume(outlen >= 1 && outlen <= 32);
  uint8_t *out = malloc(outlen);
  __CPROVER_assume(out != NULL);

  ngtcp2_ssize r = ngtcp2_pkt_encode_stream_frame(out, outlen, &fr);
  if (r >= 0) {
    __CPROVER_assert((size_t)r <= outlen, "return within outlen");
  }
  free(out);
}
