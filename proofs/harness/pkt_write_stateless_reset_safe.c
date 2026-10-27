#include <stdlib.h>
#include "ngtcp2_pkt.h"
/* ngtcp2_pkt_write_stateless_reset2: never writes past destlen nor reads
   past rand[randlen); return <= destlen. */
void harness(void) {
  size_t randlen; __CPROVER_assume(randlen <= 40);
  uint8_t *rand = malloc(randlen ? randlen : 1); __CPROVER_assume(rand != NULL);
  ngtcp2_stateless_reset_token token;   /* inline data */
  size_t destlen; __CPROVER_assume(destlen <= 80);
  uint8_t *dest = malloc(destlen ? destlen : 1); __CPROVER_assume(dest != NULL);
  ngtcp2_ssize r = ngtcp2_pkt_write_stateless_reset2(dest, destlen, &token, rand, randlen);
  if (r >= 0) __CPROVER_assert((size_t)r <= destlen, "within destlen");
  free(rand); free(dest);
}
