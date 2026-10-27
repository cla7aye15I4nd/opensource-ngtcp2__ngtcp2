#include "ngtcp2_pkt.h"
/* Theorem (RFC 9000 Section 17.1 / A.3 guarantee): if the sender's full
   packet number P lies in the window (expected - hwin, expected + hwin]
   around expected = max_pkt_num + 1, then decoding its low 8*len bits
   recovers P exactly.  Holds for every max_pkt_num in [-1, MAX_PKT_NUM]
   and every legal P in [0, MAX_PKT_NUM]. */
void harness(void) {
  int64_t max_pkt_num, P; size_t len;
  __CPROVER_assume(len >= 1 && len <= 4);
  __CPROVER_assume(max_pkt_num >= -1 && max_pkt_num <= NGTCP2_MAX_PKT_NUM);
  __CPROVER_assume(P >= 0 && P <= NGTCP2_MAX_PKT_NUM);
  __int128 expected = (__int128)max_pkt_num + 1;
  __int128 hwin = (__int128)1 << (8 * len - 1);
  __CPROVER_assume(P > expected - hwin && P <= expected + hwin);
  int64_t truncated = (int64_t)((uint64_t)P & ((1ULL << (8 * len)) - 1));
  int64_t r = ngtcp2_pkt_adjust_pkt_num(max_pkt_num, truncated, len);
  __CPROVER_assert(r == P, "decoding recovers the full packet number");
}
