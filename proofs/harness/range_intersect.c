#include "ngtcp2_range.h"
/* Lemma: ngtcp2_range_intersect computes the set intersection of two
   half-open ranges: x in r  <=>  x in a and x in b, for all x; an empty
   intersection is returned as the canonical empty range {0, 0}. Also
   ngtcp2_range_cut splits a around a sub-range b exactly. */
static int in(const ngtcp2_range *r, uint64_t x) { return r->begin <= x && x < r->end; }
void harness(void) {
  ngtcp2_range a, b; uint64_t x;
  __CPROVER_assume(a.begin <= a.end && b.begin <= b.end);
  ngtcp2_range r = ngtcp2_range_intersect(&a, &b);
  __CPROVER_assert(in(&r, x) == (in(&a, x) && in(&b, x)), "intersection semantics");
  __CPROVER_assert(r.begin < r.end || (r.begin == 0 && r.end == 0), "canonical empty");
  __CPROVER_assert(ngtcp2_range_len(&r) <= ngtcp2_range_len(&a) && ngtcp2_range_len(&r) <= ngtcp2_range_len(&b), "no growth");
  if (a.begin <= b.begin && b.end <= a.end) {
    ngtcp2_range l, rr;
    ngtcp2_range_cut(&l, &rr, &a, &b);
    __CPROVER_assert((in(&l, x) || in(&rr, x)) == (in(&a, x) && !in(&b, x)), "cut = a \\ b");
  }
}
