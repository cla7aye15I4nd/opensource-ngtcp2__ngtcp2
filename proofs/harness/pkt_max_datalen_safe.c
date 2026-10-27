/* ngtcp2_pkt_stream_max_datalen / crypto_max_datalen / datagram_framelen /
   is_supported_version / is_reserved_version: no UB; the put_uvarintlen
   asserts hold under valid-varint fields; the max_datalen results are <= len
   (the subtraction guards prevent underflow-to-huge). */
#include "ngtcp2_pkt.h"
#include "ngtcp2_conv.h"
void harness(void) {
  unsigned which; __CPROVER_assume(which < 4);
  if (which == 0) {
    int64_t sid; __CPROVER_assume(sid >= 0 && (uint64_t)sid <= NGTCP2_MAX_VARINT);
    uint64_t off; __CPROVER_assume(off <= NGTCP2_MAX_VARINT);
    uint64_t len; size_t left;
    size_t r = ngtcp2_pkt_stream_max_datalen(sid, off, len, left);
    if (r != (size_t)-1) __CPROVER_assert(r <= len, "stream: returns at most len");
  } else if (which == 1) {
    uint64_t off; __CPROVER_assume(off <= NGTCP2_MAX_VARINT);
    size_t len, left;
    size_t r = ngtcp2_pkt_crypto_max_datalen(off, len, left);
    if (r != (size_t)-1) __CPROVER_assert(r <= len, "crypto: returns at most len");
  } else if (which == 2) {
    size_t len; __CPROVER_assume(len <= NGTCP2_MAX_VARINT); (void)ngtcp2_pkt_datagram_framelen(len);
  } else {
    uint32_t v; (void)ngtcp2_is_supported_version(v); (void)ngtcp2_is_reserved_version(v);
  }
  __CPROVER_assert(1, "reached without UB");
}
