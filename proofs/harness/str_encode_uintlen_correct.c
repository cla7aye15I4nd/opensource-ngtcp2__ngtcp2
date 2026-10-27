#include "ngtcp2_str.h"
#include <stdint.h>
static size_t naive_digits(uint64_t n) { size_t d = 1; while (n >= 10) { n /= 10; ++d; } return d; }
/* Verifies the Lemire count_digit trick (countl_zero + table lookup, incl.
   the table-index bound) agrees with a naive decimal digit count for every n. */
void harness(void) {
  uint64_t n;
  __CPROVER_assert(ngtcp2_encode_uintlen(n) == naive_digits(n), "digit count correct");
}
