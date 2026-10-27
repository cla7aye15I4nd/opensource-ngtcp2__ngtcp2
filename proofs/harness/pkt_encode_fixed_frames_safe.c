#include <stdlib.h>
#include "ngtcp2_pkt.h"
#include "ngtcp2_conv.h"
/* All remaining fixed-size frame encoders: each returns NOBUF or a length
   <= outlen (no OOB write).  out is malloc'd at exactly outlen so CBMC
   --bounds-check catches any overflow; each encoder's internal
   assert((p-out)==len) is also discharged. */
#define V(x) __CPROVER_assume((x) <= NGTCP2_MAX_VARINT)
#define SID(x) __CPROVER_assume((x) >= 0 && (uint64_t)(x) <= NGTCP2_MAX_VARINT)
static uint8_t *ob(size_t *outlen) {
  size_t n; __CPROVER_assume(n >= 1 && n <= 24); *outlen = n;
  uint8_t *o = malloc(n); __CPROVER_assume(o != NULL); return o;
}
#define CHK(r, outlen) do { if ((r) >= 0) __CPROVER_assert((size_t)(r) <= (outlen), "within outlen"); } while (0)

void harness(void) {
  size_t outlen; uint8_t *out; ngtcp2_ssize r;

  { ngtcp2_reset_stream fr; SID(fr.stream_id); V(fr.app_error_code); V(fr.final_size);
    out = ob(&outlen); r = ngtcp2_pkt_encode_reset_stream_frame(out, outlen, &fr); CHK(r, outlen); free(out); }
  { ngtcp2_stop_sending fr; SID(fr.stream_id); V(fr.app_error_code);
    out = ob(&outlen); r = ngtcp2_pkt_encode_stop_sending_frame(out, outlen, &fr); CHK(r, outlen); free(out); }
  { ngtcp2_max_data fr; V(fr.max_data);
    out = ob(&outlen); r = ngtcp2_pkt_encode_max_data_frame(out, outlen, &fr); CHK(r, outlen); free(out); }
  { ngtcp2_max_stream_data fr; SID(fr.stream_id); V(fr.max_stream_data);
    out = ob(&outlen); r = ngtcp2_pkt_encode_max_stream_data_frame(out, outlen, &fr); CHK(r, outlen); free(out); }
  { ngtcp2_max_streams fr; __CPROVER_assume(fr.type==NGTCP2_FRAME_MAX_STREAMS_BIDI||fr.type==NGTCP2_FRAME_MAX_STREAMS_UNI); V(fr.max_streams);
    out = ob(&outlen); r = ngtcp2_pkt_encode_max_streams_frame(out, outlen, &fr); CHK(r, outlen); free(out); }
  { ngtcp2_data_blocked fr; V(fr.max_data);
    out = ob(&outlen); r = ngtcp2_pkt_encode_data_blocked_frame(out, outlen, &fr); CHK(r, outlen); free(out); }
  { ngtcp2_stream_data_blocked fr; SID(fr.stream_id); V(fr.max_stream_data);
    out = ob(&outlen); r = ngtcp2_pkt_encode_stream_data_blocked_frame(out, outlen, &fr); CHK(r, outlen); free(out); }
  { ngtcp2_streams_blocked fr; __CPROVER_assume(fr.type==NGTCP2_FRAME_STREAMS_BLOCKED_BIDI||fr.type==NGTCP2_FRAME_STREAMS_BLOCKED_UNI); V(fr.max_streams);
    out = ob(&outlen); r = ngtcp2_pkt_encode_streams_blocked_frame(out, outlen, &fr); CHK(r, outlen); free(out); }
  { ngtcp2_path_challenge fr;
    out = ob(&outlen); r = ngtcp2_pkt_encode_path_challenge_frame(out, outlen, &fr); CHK(r, outlen); free(out); }
  { ngtcp2_path_response fr;
    out = ob(&outlen); r = ngtcp2_pkt_encode_path_response_frame(out, outlen, &fr); CHK(r, outlen); free(out); }
  { ngtcp2_retire_connection_id fr; V(fr.seq);
    out = ob(&outlen); r = ngtcp2_pkt_encode_retire_connection_id_frame(out, outlen, &fr); CHK(r, outlen); free(out); }
}
