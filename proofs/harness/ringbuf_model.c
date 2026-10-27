#include <stdlib.h>
#include "ngtcp2_ringbuf.h"
/* Lemma: against an abstract bounded deque model, any sequence of NOPS
   push_front/push_back/pop_front/pop_back/get operations on a ring buffer
   of capacity CAP keeps len <= capacity, every returned slot is inside the
   backing buffer, and get(i) returns the i-th element of the model
   (push into a full buffer evicts from the opposite end). */
#define CAP 4
void harness(void) {
  int store[CAP];
  ngtcp2_ringbuf rb;
  ngtcp2_ringbuf_buf_init(&rb, CAP, sizeof(int), (uint8_t *)store, NULL);
  int model[CAP]; size_t mlen = 0; int next = 1;
  for (int step = 0; step < NOPS; ++step) {
    unsigned op;
    __CPROVER_assume(op < 4);
    if (op == 0) {
      int *s = ngtcp2_ringbuf_push_back(&rb);
      __CPROVER_assert((uint8_t *)s >= (uint8_t *)store && (uint8_t *)(s + 1) <= (uint8_t *)(store + CAP), "slot in buffer");
      *s = next;
      if (mlen == CAP) { for (size_t i = 0; i + 1 < CAP; ++i) model[i] = model[i + 1]; model[CAP - 1] = next; }
      else model[mlen++] = next;
      ++next;
    } else if (op == 1) {
      int *s = ngtcp2_ringbuf_push_front(&rb);
      __CPROVER_assert((uint8_t *)s >= (uint8_t *)store && (uint8_t *)(s + 1) <= (uint8_t *)(store + CAP), "slot in buffer");
      *s = next;
      size_t n = mlen == CAP ? CAP - 1 : mlen;
      for (size_t i = n; i > 0; --i) model[i] = model[i - 1];
      model[0] = next; mlen = n + 1; ++next;
    } else if (op == 2 && mlen) {
      ngtcp2_ringbuf_pop_front(&rb);
      for (size_t i = 0; i + 1 < mlen; ++i) model[i] = model[i + 1];
      --mlen;
    } else if (op == 3 && mlen) {
      ngtcp2_ringbuf_pop_back(&rb);
      --mlen;
    }
    __CPROVER_assert(ngtcp2_ringbuf_len(&rb) == mlen && mlen <= CAP, "length matches model");
    __CPROVER_assert(ngtcp2_ringbuf_full(&rb) == (mlen == CAP), "full() matches model");
    for (size_t i = 0; i < mlen; ++i)
      __CPROVER_assert(*(int *)ngtcp2_ringbuf_get(&rb, i) == model[i], "get(i) matches model");
  }
}
