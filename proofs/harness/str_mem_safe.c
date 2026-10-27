#include <stdlib.h>
#include "ngtcp2_str.h"
void harness(void) {
  size_t len; __CPROVER_assume(len <= 6);
  uint8_t *data = malloc(len ? len : 1); __CPROVER_assume(data != NULL);
  /* encode_hex writes exactly 2*len */
  uint8_t *hx = malloc(2 * (len ? len : 1)); __CPROVER_assume(hx != NULL);
  uint8_t *he = ngtcp2_encode_hex(hx, data, len);
  __CPROVER_assert((size_t)(he - hx) == 2 * len, "encode_hex writes 2*len");
  /* printable_ascii writes exactly len */
  uint8_t *pa = malloc(len ? len : 1); __CPROVER_assume(pa != NULL);
  uint8_t *pe = ngtcp2_encode_printable_ascii(pa, data, len);
  __CPROVER_assert((size_t)(pe - pa) == len, "printable writes len");
  /* cmemeq reads n bytes from each, returns 0/1 */
  uint8_t *b = malloc(len ? len : 1); __CPROVER_assume(b != NULL);
  int r = ngtcp2_cmemeq(data, b, len);
  __CPROVER_assert(r == 0 || r == 1, "cmemeq boolean");
  free(data); free(hx); free(pa); free(b);
}
