#include "prelude.h"
#define NGTCP2_LONG_TYPE_MASK 0x30
#define NGTCP2_PROTO_VER_V1 0x1u
#define NGTCP2_PROTO_VER_V2 0x6b3343cfu
#define NGTCP2_PKT_INITIAL 0x10
#define NGTCP2_PKT_0RTT 0x11
#define NGTCP2_PKT_HANDSHAKE 0x12
#define NGTCP2_PKT_RETRY 0x13
static int is_supported(uint32_t v){ return v==NGTCP2_PROTO_VER_V1||v==NGTCP2_PROTO_VER_V2; }
uint8_t ngtcp2_pkt_get_type_long(uint32_t version, uint8_t c) {
  uint8_t pkt_type = (uint8_t)((c & NGTCP2_LONG_TYPE_MASK) >> 4);
  if (version == NGTCP2_PROTO_VER_V2) {
    switch (pkt_type) { case 1: return NGTCP2_PKT_INITIAL; case 2: return NGTCP2_PKT_0RTT;
      case 3: return NGTCP2_PKT_HANDSHAKE; case 0: return NGTCP2_PKT_RETRY; default: return 0; }
  }
  if (!is_supported(version)) return 0;
  switch (pkt_type) { case 0: return NGTCP2_PKT_INITIAL; case 1: return NGTCP2_PKT_0RTT;
    case 2: return NGTCP2_PKT_HANDSHAKE; case 3: return NGTCP2_PKT_RETRY; default: return 0; }
}
