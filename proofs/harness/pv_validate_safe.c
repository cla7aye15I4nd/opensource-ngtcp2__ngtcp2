/* ngtcp2_pv_validate: iterates the path-validation ringbuf comparing the
   received PATH_RESPONSE data against stored challenges; never reads an entry
   out of bounds (ringbuf_get(i) for i<len is in-bounds; cmemeq is fixed 8B). */
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
  for (size_t i = 0; i < len; ++i) {
    (void)ngtcp2_ringbuf_push_back(&pv.ents.rb);
  }
  ngtcp2_path_challenge_data data;
  uint8_t flags;
  int r = ngtcp2_pv_validate(&pv, &flags, &data);
  __CPROVER_assert(r == 0 || r == NGTCP2_ERR_INVALID_STATE ||
                   r == NGTCP2_ERR_INVALID_ARGUMENT, "well-defined result");
}
