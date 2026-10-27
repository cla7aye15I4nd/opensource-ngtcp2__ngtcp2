#include "ngtcp2_range.h"
/* ngtcp2_range arithmetic: range_len no underflow for a valid range
   (begin<=end); range_cut preserves well-formedness when b is included
   in a; range_intersect yields a valid (possibly empty) range. */
void harness(void) {
  ngtcp2_range a, b, l, r;
  __CPROVER_assume(a.begin <= a.end);
  __CPROVER_assume(b.begin <= b.end);

  /* range_len: no underflow, equals end-begin */
  uint64_t len = ngtcp2_range_len(&a);
  __CPROVER_assert(len == a.end - a.begin && a.begin + len == a.end, "len correct");

  /* range_intersect: result is a valid range */
  ngtcp2_range is = ngtcp2_range_intersect(&a, &b);
  __CPROVER_assert(is.begin <= is.end, "intersect valid");

  /* range_cut: with b included in a, both halves are well-formed */
  __CPROVER_assume(a.begin <= b.begin && b.end <= a.end);
  ngtcp2_range_cut(&l, &r, &a, &b);
  __CPROVER_assert(l.begin <= l.end, "left valid");
  __CPROVER_assert(r.begin <= r.end, "right valid");
}
