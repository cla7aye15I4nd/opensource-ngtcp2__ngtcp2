/* Sound stub of the PCG RNG for memory-safety proofs: ngtcp2_pcg32_rand_n(pcg,n)
   is specified to return a value in [0,n) for n>0.  We model exactly that,
   dropping the (CBMC-expensive) rejection-sampling loop.  n==0 hits the real
   function's assert(n); callers must pass n>0, which we check. */
#include <stdint.h>
#include "ngtcp2_pcg.h"
uint32_t ngtcp2_pcg32_rand_n(ngtcp2_pcg32 *pcg, uint32_t n) {
  (void)pcg;
  __CPROVER_assert(n != 0, "rand_n precondition n != 0");
  uint32_t r;
  __CPROVER_assume(r < n);
  return r;
}
