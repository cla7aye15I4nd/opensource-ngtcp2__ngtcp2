/* ngtcp2_frame_chain_objalloc_new (via the proved objalloc chain) and
   extralen_new (malloc(sizeof+extralen), bounded => no size overflow); init. */
#include "ngtcp2_frame_chain.h"
#include "ngtcp2_objalloc.h"
#include "ngtcp2_mem.h"

void harness(void) {
  const ngtcp2_mem *mem = ngtcp2_mem_default();
  ngtcp2_frame_chain *frc = NULL;
  unsigned which; __CPROVER_assume(which < 2);
  if (which == 0) {
    ngtcp2_objalloc oa;
    ngtcp2_objalloc_init(&oa, 1024, mem);
    int rv = ngtcp2_frame_chain_objalloc_new(&frc, &oa);
    if (rv == 0) {
      __CPROVER_assert(frc != NULL && frc->next == NULL, "initialized");
      ngtcp2_frame_chain_objalloc_del(frc, &oa, mem);
    }
    ngtcp2_objalloc_free(&oa);
  } else {
    size_t extralen; __CPROVER_assume(extralen <= 256);
    int rv = ngtcp2_frame_chain_extralen_new(&frc, extralen, mem);
    if (rv == 0) { __CPROVER_assert(frc != NULL, "allocated"); ngtcp2_mem_free(mem, frc); }
  }
}
