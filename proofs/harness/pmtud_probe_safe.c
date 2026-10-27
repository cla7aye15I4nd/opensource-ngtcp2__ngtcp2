#include <stdlib.h>
#include "ngtcp2_pmtud.h"
/* ngtcp2_pmtud_probe_success / pmtud_next_probe never read probes[] out of
   bounds: with an active probe (mtu_idx < probeslen) the index stays within
   [0, probeslen] across advancement. */
void harness(void) {
  size_t P; __CPROVER_assume(P >= 1 && P <= 4);
  uint16_t *probes = malloc(sizeof(uint16_t) * P); __CPROVER_assume(probes != NULL);
  ngtcp2_pmtud pmtud;
  pmtud.probes = probes;
  pmtud.probeslen = P;
  __CPROVER_assume(pmtud.mtu_idx < P);
  size_t payloadlen;
  ngtcp2_pmtud_probe_success(&pmtud, payloadlen);
  __CPROVER_assert(pmtud.mtu_idx <= P, "mtu_idx within bounds after success");
  free(probes);
}
