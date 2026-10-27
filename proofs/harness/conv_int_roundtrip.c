#include "ngtcp2_conv.h"
/* Roundtrip + exact-length for the big-endian integer codec and pkt_num,
   and a basic property of ord_stream_id. */
void harness(void) {
  { uint64_t n; uint8_t b[8]; uint8_t *e = ngtcp2_put_uint64be(b, n);
    uint64_t v; const uint8_t *g = ngtcp2_get_uint64be(&v, b);
    __CPROVER_assert(v == n && e == b + 8 && g == b + 8, "u64be roundtrip+len"); }
  { uint32_t n; uint8_t b[4]; uint8_t *e = ngtcp2_put_uint32be(b, n);
    uint32_t v; const uint8_t *g = ngtcp2_get_uint32be(&v, b);
    __CPROVER_assert(v == n && e == b + 4 && g == b + 4, "u32be roundtrip+len"); }
  { uint32_t n; __CPROVER_assume(n < (1u << 24)); uint8_t b[3];
    uint8_t *e = ngtcp2_put_uint24be(b, n); uint32_t v; const uint8_t *g = ngtcp2_get_uint24be(&v, b);
    __CPROVER_assert(v == n && e == b + 3 && g == b + 3, "u24be roundtrip+len"); }
  { uint16_t n; uint8_t b[2]; uint8_t *e = ngtcp2_put_uint16be(b, n);
    uint16_t v; const uint8_t *g = ngtcp2_get_uint16be(&v, b);
    __CPROVER_assert(v == n && e == b + 2 && g == b + 2, "u16be roundtrip+len"); }
  { size_t len; __CPROVER_assume(len >= 1 && len <= 4);
    int64_t pn; __CPROVER_assume(pn >= 0 && (uint64_t)pn < ((uint64_t)1 << (8 * len)));
    uint8_t b[4]; uint8_t *e = ngtcp2_put_pkt_num(b, pn, len);
    int64_t v = ngtcp2_get_pkt_num(b, len);
    __CPROVER_assert(v == pn && e == b + len, "pkt_num roundtrip+len"); }
  { int64_t sid; __CPROVER_assume(sid >= 0);
    __CPROVER_assert(ngtcp2_ord_stream_id(sid) >= 1, "ord_stream_id >= 1"); }
}
