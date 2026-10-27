#include <stdlib.h>
#include "ngtcp2_ppe.h"
#include <ngtcp2/ngtcp2.h>
/* ngtcp2_ppe_dgram_padding_size: same guarded padding write as
   ppe_padding_size but relative to the datagram offset; prove in-bounds. */
void harness(void) {
  size_t cap; __CPROVER_assume(cap >= 1 && cap <= 64);
  uint8_t *out = malloc(cap); __CPROVER_assume(out != NULL);
  ngtcp2_crypto_cc cc;
  size_t overhead; __CPROVER_assume(overhead <= 32);
  cc.aead.max_overhead = overhead;
  size_t dgram_off; __CPROVER_assume(dgram_off <= 1500);
  ngtcp2_ppe ppe;
  ngtcp2_ppe_init(&ppe, out, cap, dgram_off, &cc);
  size_t w; __CPROVER_assume(w <= cap);
  __CPROVER_assume(w + overhead <= cap);
  ppe.buf.last = out + w;
  size_t pno; __CPROVER_assume(pno + 4 + NGTCP2_HP_SAMPLELEN <= cap);
  __CPROVER_assume(pno <= w);
  ppe.pkt_num_offset = pno;
  size_t n;
  size_t r = ngtcp2_ppe_dgram_padding_size(&ppe, n);
  __CPROVER_assert(ppe.buf.last <= ppe.buf.end, "dgram padding write within buffer");
  free(out);
}
