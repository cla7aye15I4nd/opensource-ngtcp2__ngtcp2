/* Public default-setters: ngtcp2_settings_default / transport_params_default
   write only within the caller-provided struct (no OOB). */
#include <ngtcp2/ngtcp2.h>

void harness(void) {
  unsigned which; __CPROVER_assume(which < 2);
  if (which == 0) {
    ngtcp2_settings s;
    ngtcp2_settings_default(&s);
  } else {
    ngtcp2_transport_params p;
    ngtcp2_transport_params_default(&p);
  }
  __CPROVER_assert(1, "reached without OOB");
}
