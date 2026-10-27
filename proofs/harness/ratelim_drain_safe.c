#include "ngtcp2_ratelim.h"
#include <ngtcp2/ngtcp2.h>
/* ngtcp2_ratelim_drain/ratelim_update: no div-by-zero, and the token-bucket
   invariant (carry < NGTCP2_SECONDS, tokens <= burst) is preserved across a
   step for any rate/n and any ts >= rlim->ts.  The overflow guard
   `rate <= (UINT64_MAX-carry)/d` is what keeps gain = rate*d+carry from
   wrapping; if it were wrong the invariant asserts below would catch it. */
void harness(void) {
  ngtcp2_ratelim rlim;
  __CPROVER_assume(rlim.carry < NGTCP2_SECONDS);
  __CPROVER_assume(rlim.burst <= NGTCP2_RATELIM_MAX_BURST);
  __CPROVER_assume(rlim.tokens <= rlim.burst);
  ngtcp2_tstamp ts; __CPROVER_assume(ts >= rlim.ts);
  uint64_t n;
  int r = ngtcp2_ratelim_drain(&rlim, n, ts);
  __CPROVER_assert(rlim.carry < NGTCP2_SECONDS, "carry < SECONDS preserved");
  __CPROVER_assert(rlim.tokens <= rlim.burst, "tokens <= burst preserved");
  __CPROVER_assert(r == 0 || r == -1, "drain result boolean");
}
