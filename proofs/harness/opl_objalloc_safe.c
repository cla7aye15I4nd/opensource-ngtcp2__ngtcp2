/* ngtcp2_opl push/pop/clear (LIFO free-list, pointer ops only) and
   ngtcp2_objalloc init/clear/free (delegate to proved balloc + opl). */
#include "ngtcp2_opl.h"
#include "ngtcp2_objalloc.h"
#include "ngtcp2_mem.h"

void harness(void) {
  unsigned which; __CPROVER_assume(which < 2);
  if (which == 0) {
    ngtcp2_opl opl; ngtcp2_opl_init(&opl);
    ngtcp2_opl_entry e1, e2;
    ngtcp2_opl_push(&opl, &e1);
    ngtcp2_opl_push(&opl, &e2);
    __CPROVER_assert(ngtcp2_opl_pop(&opl) == &e2, "LIFO 1");
    __CPROVER_assert(ngtcp2_opl_pop(&opl) == &e1, "LIFO 2");
    __CPROVER_assert(ngtcp2_opl_pop(&opl) == NULL, "empty");
  } else {
    const ngtcp2_mem *mem = ngtcp2_mem_default();
    ngtcp2_objalloc oa;
    ngtcp2_objalloc_init(&oa, 256, mem);
    ngtcp2_objalloc_clear(&oa);
    ngtcp2_objalloc_free(&oa);
  }
}
