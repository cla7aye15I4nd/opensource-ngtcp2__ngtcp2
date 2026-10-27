#include "ngtcp2_pkt.h"
/* Lemma: ngtcp2_pkt_adjust_pkt_num agrees with the reference algorithm
   of RFC 9000 Appendix A.3 for every reachable input, and never trips its
   internal assertion.  Precondition: max_pkt_num is a packet number that
   was already accepted, i.e. -1 <= max_pkt_num <= NGTCP2_MAX_PKT_NUM. */
static uint64_t rfc_decode(uint64_t largest_pn, uint64_t truncated_pn, unsigned pn_nbits) {
  uint64_t expected_pn = largest_pn + 1; /* largest_pn may be "-1" */
  uint64_t pn_win = 1ULL << pn_nbits;
  uint64_t pn_hwin = pn_win / 2;
  uint64_t pn_mask = pn_win - 1;
  uint64_t candidate_pn = (expected_pn & ~pn_mask) | truncated_pn;
  /* RFC: candidate_pn <= expected_pn - pn_hwin (signed arithmetic) */
  if ((__int128)candidate_pn <= (__int128)expected_pn - (__int128)pn_hwin &&
      candidate_pn < (1ULL << 62) - pn_win)
    return candidate_pn + pn_win;
  if (candidate_pn > expected_pn + pn_hwin && candidate_pn >= pn_win)
    return candidate_pn - pn_win;
  return candidate_pn;
}
void harness(void) {
  int64_t max_pkt_num, pkt_num; size_t pkt_numlen;
  __CPROVER_assume(pkt_numlen >= 1 && pkt_numlen <= 4);
  __CPROVER_assume(max_pkt_num >= -1 && max_pkt_num <= NGTCP2_MAX_PKT_NUM);
  __CPROVER_assume(pkt_num >= 0 && (uint64_t)pkt_num < (1ULL << (8 * pkt_numlen)));
  int64_t r = ngtcp2_pkt_adjust_pkt_num(max_pkt_num, pkt_num, pkt_numlen);
  uint64_t ref = rfc_decode((uint64_t)max_pkt_num, (uint64_t)pkt_num, (unsigned)(8 * pkt_numlen));
  __CPROVER_assert((uint64_t)r == ref || (r > NGTCP2_MAX_PKT_NUM), "agrees with RFC 9000 A.3 (or is rejected by caller)");
  __CPROVER_assert(((uint64_t)r & ((1ULL << (8 * pkt_numlen)) - 1)) == (uint64_t)pkt_num, "result has the received low bits");
}
