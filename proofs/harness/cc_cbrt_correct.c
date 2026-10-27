/* ngtcp2_cbrt (digit-by-digit integer cube root): prove y^3 <= n < (y+1)^3
   for n in a range where the cubes fit uint64, and no undefined shift / UB
   for the computation.  (cc.c logging neutralized via include technique.) */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_cc.c"

void harness(void) {
  uint64_t n; __CPROVER_assume(n <= 100000);     /* (y+1)^3 fits uint64 */
  uint64_t y = ngtcp2_cbrt(n);
  __CPROVER_assert(y * y * y <= n, "y^3 <= n");
  __CPROVER_assert(n < (y + 1) * (y + 1) * (y + 1), "n < (y+1)^3");
}
