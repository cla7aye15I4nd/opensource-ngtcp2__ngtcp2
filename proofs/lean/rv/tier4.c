#include "prelude.h"
#define NGTCP2_HEADER_FORM_BIT 0x80
#define NGTCP2_LONG_RESERVED_BIT_MASK 0x0c
#define NGTCP2_SHORT_RESERVED_BIT_MASK 0x18
#define NGTCP2_ERR_PROTO -201
int ngtcp2_pkt_verify_reserved_bits(uint8_t c) {
  if (c & NGTCP2_HEADER_FORM_BIT) {
    return (c & NGTCP2_LONG_RESERVED_BIT_MASK) == 0 ? 0 : NGTCP2_ERR_PROTO;
  }
  return (c & NGTCP2_SHORT_RESERVED_BIT_MASK) == 0 ? 0 : NGTCP2_ERR_PROTO;
}
