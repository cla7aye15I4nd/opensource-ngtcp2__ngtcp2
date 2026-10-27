/* ngtcp2_crypto_create_nonce: copies the iv then XORs its last 8 bytes with the
   packet number; no OOB for dest/iv of length ivlen >= 8 (the asserted
   precondition). */
#include <stdlib.h>
#include "ngtcp2_crypto.h"

void harness(void) {
  size_t ivlen; __CPROVER_assume(ivlen >= 8 && ivlen <= 16);
  uint8_t *iv = malloc(ivlen);
  uint8_t *dest = malloc(ivlen);
  __CPROVER_assume(iv != NULL && dest != NULL);
  int64_t pkt_num;
  ngtcp2_crypto_create_nonce(dest, iv, ivlen, pkt_num);
  __CPROVER_assert(1, "reached without OOB");
  free(iv); free(dest);
}
