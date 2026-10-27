/* ngtcp2_strerror / ngtcp2_err_infer_quic_transport_error_code: switch over an
   int returning a string literal / a code; no UB for any input. */
#include "ngtcp2_err.h"
void harness(void) {
  int liberr;
  unsigned which; __CPROVER_assume(which < 2);
  if (which == 0) { const char *s = ngtcp2_strerror(liberr); __CPROVER_assert(s != 0, "non-null"); }
  else (void)ngtcp2_err_infer_quic_transport_error_code(liberr);
  __CPROVER_assert(1, "reached without UB");
}
