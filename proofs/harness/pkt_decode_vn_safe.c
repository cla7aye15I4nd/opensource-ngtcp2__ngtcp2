/* ngtcp2_pkt_decode_version_negotiation (reads payloadlen/4 big-endian version
   numbers from an untrusted VN packet; no OOB given dest sized payloadlen/4)
   and ngtcp2_pkt_verify_reserved_bits (byte predicate). */
#include <stdlib.h>
#include "ngtcp2_pkt.h"

void harness(void) {
  unsigned which; __CPROVER_assume(which < 2);
  if (which == 0) {
    size_t n; __CPROVER_assume(n <= 6);
    size_t payloadlen = n * 4;
    uint8_t *payload = malloc(payloadlen ? payloadlen : 1);
    uint32_t *dest = malloc((n ? n : 1) * sizeof(uint32_t));
    __CPROVER_assume(payload != NULL && dest != NULL);
    size_t r = ngtcp2_pkt_decode_version_negotiation(dest, payload, payloadlen);
    __CPROVER_assert(r == n, "returns version count");
    free(payload); free(dest);
  } else {
    uint8_t c;
    int r = ngtcp2_pkt_verify_reserved_bits(c);
    __CPROVER_assert(r == 0 || r == NGTCP2_ERR_PROTO, "well-defined");
  }
}
