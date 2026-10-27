#include "prelude.h"
size_t ngtcp2_put_uvarintlen(uint64_t n) {
  if (n < 64) {
    return 1;
  }
  if (n < 16384) {
    return 2;
  }
  if (n < 1073741824) {
    return 4;
  }
  assert(n < 4611686018427387904ULL);
  return 8;
}

size_t ngtcp2_get_uvarintlen(const uint8_t *p) {
  return (size_t)(1U << (*p >> 6));
}

const uint8_t *ngtcp2_get_uvarint(uint64_t *dest, const uint8_t *p) {
  uint16_t n16;
  uint32_t n32;
  uint64_t n64;

  switch (*p >> 6) {
  case 0:
    *dest = *p++;
    return p;
  case 1:
    memcpy(&n16, p, 2);
    n16 = ngtcp2_ntohs(n16);
    n16 &= 0x3FFFU;
    *dest = n16;

    return p + 2;
  case 2:
    memcpy(&n32, p, 4);
    n32 = ngtcp2_ntohl(n32);
    n32 &= 0x3FFFFFFFU;
    *dest = n32;

    return p + 4;
  case 3:
    memcpy(&n64, p, 8);
    n64 = ngtcp2_ntohl64(n64);
    n64 &= 0x3FFFFFFFFFFFFFFFU;
    *dest = n64;

    return p + 8;
  default:
    ngtcp2_unreachable();
  }
}

static uint8_t *ngtcp2_put_uint16be(uint8_t *p, uint16_t n) {
  n = ngtcp2_htons(n);
  return ngtcp2_cpymem(p, (const uint8_t *)&n, sizeof(n));
}

static uint8_t *ngtcp2_put_uint32be(uint8_t *p, uint32_t n) {
  n = ngtcp2_htonl(n);
  return ngtcp2_cpymem(p, (const uint8_t *)&n, sizeof(n));
}

static uint8_t *ngtcp2_put_uint64be(uint8_t *p, uint64_t n) {
  n = ngtcp2_htonl64(n);
  return ngtcp2_cpymem(p, (const uint8_t *)&n, sizeof(n));
}

uint8_t *ngtcp2_put_uvarint(uint8_t *p, uint64_t n) {
  uint8_t *rv;
  if (n < 64) {
    *p++ = (uint8_t)n;
    return p;
  }
  if (n < 16384) {
    rv = ngtcp2_put_uint16be(p, (uint16_t)n);
    *p |= 0x40U;
    return rv;
  }
  if (n < 1073741824) {
    rv = ngtcp2_put_uint32be(p, (uint32_t)n);
    *p |= 0x80U;
    return rv;
  }
  assert(n < 4611686018427387904ULL);
  rv = ngtcp2_put_uint64be(p, n);
  *p |= 0xC0U;
  return rv;
}

void ngtcp2_range_init(ngtcp2_range *r, uint64_t begin, uint64_t end) {
  *r = (ngtcp2_range){
    .begin = begin,
    .end = end,
  };
}

ngtcp2_range ngtcp2_range_intersect(const ngtcp2_range *a,
                                    const ngtcp2_range *b) {
  ngtcp2_range r;
  uint64_t begin = ngtcp2_max(a->begin, b->begin);
  uint64_t end = ngtcp2_min(a->end, b->end);

  if (begin < end) {
    ngtcp2_range_init(&r, begin, end);
  } else {
    r = (ngtcp2_range){0};
  }

  return r;
}

