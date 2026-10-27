#include <stdlib.h>
#include "ngtcp2_pkt.h"
/* ngtcp2_pkt_write_version_negotiation: no write past destlen; internal
   length invariant holds. CID lengths <256 (asserts), nsv bounded. */
void harness(void) {
  size_t dcidlen, scidlen, nsv;
  __CPROVER_assume(dcidlen <= 20 && scidlen <= 20 && nsv <= 3);
  uint8_t *dcid = malloc(dcidlen ? dcidlen : 1);
  uint8_t *scid = malloc(scidlen ? scidlen : 1);
  uint32_t *sv = malloc(sizeof(uint32_t) * (nsv ? nsv : 1));
  __CPROVER_assume(dcid && scid && sv);
  size_t destlen; __CPROVER_assume(destlen <= 80);
  uint8_t *dest = malloc(destlen ? destlen : 1); __CPROVER_assume(dest != NULL);
  ngtcp2_ssize r = ngtcp2_pkt_write_version_negotiation(dest, destlen, 0, dcid,
                                                        dcidlen, scid, scidlen, sv, nsv);
  if (r >= 0) __CPROVER_assert((size_t)r <= destlen, "within destlen");
  free(dcid); free(scid); free(sv); free(dest);
}
