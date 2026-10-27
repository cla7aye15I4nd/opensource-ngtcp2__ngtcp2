#include <stdlib.h>
#include "ngtcp2_pq.h"
/* ngtcp2_pq_remove: no OOB access of pq->q for removing any item of a
   length 1..3 heap.  Memory safety is independent of the comparator's
   semantics (bubble_up strictly decreases index; bubble_down is guarded by
   j>=length), so a minimal field-only comparator is used to keep the SAT
   encoding small.  q is malloc'd at exactly `length`. */
static int less(const ngtcp2_pq_entry *a, const ngtcp2_pq_entry *b) {
  return a->index < b->index;
}
void harness(void) {
  size_t L; __CPROVER_assume(L >= 1 && L <= 3);
  size_t k; __CPROVER_assume(k < L);
  static ngtcp2_pq_entry es[3];
  ngtcp2_pq_entry **q = malloc(sizeof(ngtcp2_pq_entry *) * L);
  __CPROVER_assume(q != NULL);
  for (size_t i = 0; i < L; ++i) { es[i].index = i; q[i] = &es[i]; }
  ngtcp2_pq pq = { .q = q, .mem = NULL, .length = L, .capacity = L, .less = less };
  ngtcp2_pq_remove(&pq, &es[k]);
  free(q);
}
