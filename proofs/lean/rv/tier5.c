#include "prelude.h"
#define NGTCP2_RESERVED_VERSION_MASK 0x0a0a0a0a
#define NGTCP2_PROTO_VER_V1 0x1u
#define NGTCP2_PROTO_VER_V2 0x6b3343cfu
int ngtcp2_is_reserved_version(uint32_t version) {
  return (version & NGTCP2_RESERVED_VERSION_MASK) == NGTCP2_RESERVED_VERSION_MASK;
}
int ngtcp2_is_supported_version(uint32_t version) {
  switch (version) {
  case NGTCP2_PROTO_VER_V1:
  case NGTCP2_PROTO_VER_V2:
    return 1;
  default:
    return 0;
  }
}
