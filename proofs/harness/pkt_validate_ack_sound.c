#include "ngtcp2_pkt.h"
/* Lemma: if ngtcp2_pkt_validate_ack accepts an ACK frame (any values a
   decoder can produce, i.e. varints), then every acknowledged range it
   describes is a non-empty interval of packet numbers inside
   [min_pkt_num, largest_ack], ranges are strictly decreasing and
   separated by a gap of at least one, and no signed overflow occurs. */
void harness(void) {
  ngtcp2_ack fr;
  ngtcp2_ack_range ranges[NRANGES];
  int64_t min_pkt_num;
  fr.ranges = ranges;
  __CPROVER_assume(fr.rangecnt <= NRANGES);
  __CPROVER_assume(fr.largest_ack >= 0 && fr.largest_ack <= NGTCP2_MAX_PKT_NUM);
  __CPROVER_assume(fr.first_ack_range <= NGTCP2_MAX_VARINT);
  __CPROVER_assume(min_pkt_num >= 0 && min_pkt_num <= NGTCP2_MAX_PKT_NUM);
  for (size_t i = 0; i < NRANGES; ++i)
    __CPROVER_assume(ranges[i].gap <= NGTCP2_MAX_VARINT && ranges[i].len <= NGTCP2_MAX_VARINT);
  if (ngtcp2_pkt_validate_ack(&fr, min_pkt_num) != 0) return;
  /* Reference semantics, RFC 9000 Section 19.3.1, in 128-bit arithmetic. */
  __int128 hi = fr.largest_ack, lo = hi - (__int128)fr.first_ack_range;
  __CPROVER_assert(lo >= min_pkt_num && lo <= hi, "first range inside [min, largest]");
  for (size_t i = 0; i < fr.rangecnt; ++i) {
    __int128 nhi = lo - (__int128)ranges[i].gap - 2;
    __int128 nlo = nhi - (__int128)ranges[i].len;
    __CPROVER_assert(nhi < lo - 1, "gap of at least one unacked packet");
    __CPROVER_assert(nlo >= min_pkt_num && nlo <= nhi, "range inside [min, previous)");
    lo = nlo;
  }
}
