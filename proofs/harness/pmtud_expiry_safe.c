#include <stdlib.h>
#include "ngtcp2_pmtud.h"
/* ngtcp2_pmtud_handle_expiry reads probes[mtu_idx] then may advance; with an
   active probe it never reads out of bounds. */
void harness(void) {
  size_t P; __CPROVER_assume(P >= 1 && P <= 4);
  uint16_t *probes = malloc(sizeof(uint16_t) * P); __CPROVER_assume(probes != NULL);
  ngtcp2_pmtud pmtud;
  pmtud.probes = probes;
  pmtud.probeslen = P;
  __CPROVER_assume(pmtud.mtu_idx < P);
  ngtcp2_tstamp ts;
  __CPROVER_assume(ts >= pmtud.expiry);   /* expiry reached */
  ngtcp2_pmtud_handle_expiry(&pmtud, ts);
  __CPROVER_assert(pmtud.mtu_idx <= P, "mtu_idx within bounds after expiry");
  free(probes);
}
