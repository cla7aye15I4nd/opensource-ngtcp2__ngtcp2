#include <stdlib.h>
#include "ngtcp2_ppe.h"
#include <ngtcp2/ngtcp2.h>
/* ngtcp2_ppe_padding_size writes `len` zero bytes at buf->last, guarded by
   assert(buf_left >= len + aead.max_overhead).  Prove the assert holds and the
   write stays in-bounds, under the invariants the ppe maintains:
     - pos == begin (set by ppe_init, never moved while encoding)
     - written + overhead <= cap  (AEAD overhead kept reserved via ngtcp2_ppe_left)
     - pkt_num_offset + 4 + HP_SAMPLELEN <= cap  (encode_hd reserves HP-sample room)
   If these invariants did NOT imply safety, CBMC would return a #12-style
   counterexample (release build => OOB write). */
void harness(void) {
  size_t cap; __CPROVER_assume(cap >= 1 && cap <= 64);
  uint8_t *out = malloc(cap); __CPROVER_assume(out != NULL);

  ngtcp2_crypto_cc cc;
  size_t overhead; __CPROVER_assume(overhead <= 32);
  cc.aead.max_overhead = overhead;

  ngtcp2_ppe ppe;
  ngtcp2_ppe_init(&ppe, out, cap, 0, &cc);     /* pos=last=begin=out, end=out+cap */

  size_t w; __CPROVER_assume(w <= cap);         /* bytes already written */
  __CPROVER_assume(w + overhead <= cap);        /* AEAD overhead reserved */
  ppe.buf.last = out + w;

  size_t pno; __CPROVER_assume(pno + 4 + NGTCP2_HP_SAMPLELEN <= cap); /* HP sample fits */
  __CPROVER_assume(pno <= w);
  ppe.pkt_num_offset = pno;

  size_t n;
  size_t r = ngtcp2_ppe_padding_size(&ppe, n);
  __CPROVER_assert(ppe.buf.last <= ppe.buf.end, "padding write stays within buffer");
  __CPROVER_assert(r <= cap, "padding length sane");
  free(out);
}
