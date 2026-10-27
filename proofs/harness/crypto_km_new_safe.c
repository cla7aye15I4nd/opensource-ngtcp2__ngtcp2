/* ngtcp2_crypto_km_new / km_nocopy_new: the inline-allocated key material
   (malloc(sizeof(km)+secretlen+ivlen)) holds the secret and iv copies without
   OOB, for bounded secret/iv lengths (no size_t overflow in the allocation). */
#include <stdlib.h>
#include "ngtcp2_crypto.h"
#include "ngtcp2_mem.h"

void harness(void) {
  const ngtcp2_mem *mem = ngtcp2_mem_default();
  size_t secretlen, ivlen;
  __CPROVER_assume(secretlen <= 64 && ivlen <= 64);
  uint8_t *secret = malloc(secretlen ? secretlen : 1);
  uint8_t *iv = malloc(ivlen ? ivlen : 1);
  __CPROVER_assume(secret != NULL && iv != NULL);
  ngtcp2_crypto_aead_ctx aead_ctx;
  ngtcp2_crypto_km *ckm = NULL;
  int rv = ngtcp2_crypto_km_new(&ckm, secret, secretlen, &aead_ctx, iv, ivlen, mem);
  if (rv == 0) {
    __CPROVER_assert(ckm != NULL, "km allocated on success");
    ngtcp2_crypto_km_del(ckm, mem);
  }
  free(secret); free(iv);
}
