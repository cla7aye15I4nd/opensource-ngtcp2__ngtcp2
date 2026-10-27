/* ngtcp2_version (returns a static info struct or NULL) and
   ngtcp2_pkt_get_type_long (header-byte -> packet type map): no UB. */
#include "ngtcp2_pkt.h"
#include <ngtcp2/ngtcp2.h>
void harness(void) {
  unsigned which; __CPROVER_assume(which < 2);
  if (which == 0) { int lv; (void)ngtcp2_version(lv); }
  else { uint32_t v; uint8_t c; (void)ngtcp2_pkt_get_type_long(v, c); }
  __CPROVER_assert(1, "reached without UB");
}
