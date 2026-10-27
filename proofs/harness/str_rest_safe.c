/* Remaining str.c: setmem/secure_clear/get_bytes (sized copies) and
   encode_ipv4/encode_ipv6 (format into a buffer >= max output). No OOB. */
#include <stdlib.h>
#include "ngtcp2_str.h"
#include <ngtcp2/ngtcp2.h>
void harness(void) {
  unsigned which; __CPROVER_assume(which < 4);
  if (which == 0) { size_t n; __CPROVER_assume(n <= 16); uint8_t *d = malloc(n ? n : 1); uint8_t b; __CPROVER_assume(d); ngtcp2_setmem(d, b, n); free(d); }
  else if (which == 1) { size_t n; __CPROVER_assume(n <= 16); uint8_t *d = malloc(n ? n : 1); __CPROVER_assume(d); ngtcp2_secure_clear(d, n); free(d); }
  else if (which == 2) { size_t n; __CPROVER_assume(n <= 16); uint8_t *d = malloc(n ? n : 1); uint8_t *s = malloc(n ? n : 1); __CPROVER_assume(d && s); (void)ngtcp2_get_bytes(d, s, n); free(d); free(s); }
  else if (which == 3) { uint8_t *d = malloc(64); __CPROVER_assume(d); ngtcp2_in_addr a; (void)ngtcp2_encode_ipv4(d, &a); free(d); }
  else { uint8_t *d = malloc(64); __CPROVER_assume(d); ngtcp2_in6_addr a; (void)ngtcp2_encode_ipv6(d, &a); free(d); }
  __CPROVER_assert(1, "reached without UB");
}
