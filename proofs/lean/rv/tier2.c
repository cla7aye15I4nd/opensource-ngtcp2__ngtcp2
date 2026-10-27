#include "prelude.h"
uint64_t ngtcp2_ord_stream_id(int64_t stream_id) {
  return (uint64_t)(stream_id >> 2) + 1;
}
uint64_t ngtcp2_range_len(const ngtcp2_range *r) {
  return r->end - r->begin;
}
int ngtcp2_range_eq(const ngtcp2_range *a, const ngtcp2_range *b) {
  return a->begin == b->begin && a->end == b->end;
}
