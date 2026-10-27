#include <stdlib.h>
#include "ngtcp2_pq.h"
/* ngtcp2_pq_pop: no OOB access of pq->q for any heap of length 1..4.
   q is malloc'd at exactly `length` so any index >= length is caught. */
typedef struct { ngtcp2_pq_entry pe; uint64_t key; } ent;
static int less(const ngtcp2_pq_entry *a, const ngtcp2_pq_entry *b) {
  return ((const ent *)a)->key < ((const ent *)b)->key;
}
void harness(void) {
  size_t L; __CPROVER_assume(L >= 1 && L <= 4);
  static ent es[4];
  ngtcp2_pq_entry **q = malloc(sizeof(ngtcp2_pq_entry *) * L);
  __CPROVER_assume(q != NULL);
  for (size_t i = 0; i < L; ++i) { es[i].pe.index = i; q[i] = &es[i].pe; }
  ngtcp2_pq pq = { .q = q, .mem = NULL, .length = L, .capacity = L, .less = less };
  ngtcp2_pq_pop(&pq);
  free(q);
}
