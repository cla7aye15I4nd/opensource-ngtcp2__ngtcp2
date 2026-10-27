/* Remaining pv functions: add_entry/handle_entry_expiry/should_send_probe/
   validation_timed_out/next_expiry/cancel_expired_timer — ringbuf-backed,
   no OOB access. */
#include "ngtcp2_log.h"
#undef ngtcp2_log_infof
#undef ngtcp2_log_info
#define ngtcp2_log_infof(...) do { } while (0)
#define ngtcp2_log_info(...) do { } while (0)
#include "ngtcp2_pv.c"

void harness(void) {
  ngtcp2_pv pv;
  ngtcp2_static_ringbuf_pv_ents_init(&pv.ents);
  size_t len; __CPROVER_assume(len <= NGTCP2_PV_MAX_ENTRIES);
  for (size_t i = 0; i < len; ++i) (void)ngtcp2_ringbuf_push_back(&pv.ents.rb);
  __CPROVER_assume(pv.probe_pkt_left >= 1);
  ngtcp2_tstamp ts;
  unsigned which; __CPROVER_assume(which < 6);
  switch (which) {
  case 0: {
    ngtcp2_path_challenge_data data; ngtcp2_tstamp expiry; uint8_t flags;
    ngtcp2_pv_add_entry(&pv, &data, expiry, flags, ts); break;
  }
  case 1: ngtcp2_pv_handle_entry_expiry(&pv, ts); break;
  case 2: (void)ngtcp2_pv_should_send_probe(&pv); break;
  case 3:
    __CPROVER_assume(len >= 1);  /* precondition: active validation */
    (void)ngtcp2_pv_validation_timed_out(&pv, ts); break;
  case 4: (void)ngtcp2_pv_next_expiry(&pv); break;
  default: ngtcp2_pv_cancel_expired_timer(&pv, ts); break;
  }
  __CPROVER_assert(1, "reached without UB");
}
