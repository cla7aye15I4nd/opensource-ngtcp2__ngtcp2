#include <stdlib.h>
#include "ngtcp2_pkt.h"
/* Lemma family (instantiated per frame type via -DFTYPE_LO/-DFTYPE_HI):
   for EVERY adversarial payload of length 0 < payloadlen <= MAXLEN whose
   first byte is a frame type in [FTYPE_LO, FTYPE_HI], the frame decoder
     (1) performs no out-of-bounds read, UB, or failed internal assert,
     (2) returns an error or a length 1 <= rv <= payloadlen,
     (3) on success, every pointer it hands back lies inside the bytes it
         claims to have consumed, payload[0, rv). */
#ifndef MAXLEN
#  define MAXLEN 16
#endif
static int inside(const uint8_t *base, size_t n, const uint8_t *pl, ngtcp2_ssize rv) {
  return n == 0 || (base >= pl && base + n <= pl + rv);
}
void harness(void) {
  size_t payloadlen;
  __CPROVER_assume(payloadlen >= 1 && payloadlen <= MAXLEN);
  uint8_t *payload = malloc(payloadlen);
  __CPROVER_assume(payload != NULL);
  __CPROVER_assume(payload[0] >= FTYPE_LO && payload[0] <= FTYPE_HI);
  ngtcp2_frame_decoder frd;
  ngtcp2_frame fr;
  ngtcp2_ssize rv = ngtcp2_frame_decoder_decode(&frd, &fr, payload, payloadlen);
  if (rv < 0) {
    __CPROVER_assert(rv == NGTCP2_ERR_FRAME_ENCODING, "only FRAME_ENCODING errors");
    return;
  }
  __CPROVER_assert(rv >= 1 && (size_t)rv <= payloadlen, "consumed length within payload");
  uint8_t t = payload[0];
  if ((t & 0xf8) == NGTCP2_FRAME_STREAM || t == NGTCP2_FRAME_CRYPTO ||
      t == NGTCP2_FRAME_DATAGRAM || t == NGTCP2_FRAME_DATAGRAM_LEN) {
    size_t cnt = t >= NGTCP2_FRAME_DATAGRAM ? fr.datagram.datacnt : fr.stream.datacnt;
    ngtcp2_vec *v = t >= NGTCP2_FRAME_DATAGRAM ? fr.datagram.data : fr.stream.data;
    __CPROVER_assert(cnt <= 1, "datacnt <= 1");
    if (cnt) {
      __CPROVER_assert(v == &frd.buf.data, "data vec is decoder-owned");
      __CPROVER_assert(inside(v->base, v->len, payload, rv), "stream/crypto/datagram data in bounds");
    }
    if (t != NGTCP2_FRAME_DATAGRAM && t != NGTCP2_FRAME_DATAGRAM_LEN)
      __CPROVER_assert(fr.stream.offset <= NGTCP2_MAX_VARINT, "offset is a varint");
  } else if (t == NGTCP2_FRAME_ACK || t == NGTCP2_FRAME_ACK_ECN) {
    __CPROVER_assert(fr.ack.rangecnt <= NGTCP2_MAX_ACK_RANGES, "ack rangecnt bounded by buffer");
    __CPROVER_assert(fr.ack.ranges == frd.buf.ack_ranges, "ranges are decoder-owned");
    __CPROVER_assert(fr.ack.largest_ack >= 0, "largest_ack non-negative");
  } else if (t == NGTCP2_FRAME_NEW_TOKEN) {
    __CPROVER_assert(inside(fr.new_token.token, fr.new_token.tokenlen, payload, rv), "token in bounds");
  } else if (t == NGTCP2_FRAME_CONNECTION_CLOSE || t == NGTCP2_FRAME_CONNECTION_CLOSE_APP) {
    __CPROVER_assert(inside(fr.connection_close.reason, fr.connection_close.reasonlen, payload, rv), "reason in bounds");
  } else if (t == NGTCP2_FRAME_NEW_CONNECTION_ID) {
    __CPROVER_assert(fr.new_connection_id.cid.datalen >= 1 && fr.new_connection_id.cid.datalen <= NGTCP2_MAX_CIDLEN, "cid length 1..20");
  } else if (t == NGTCP2_FRAME_PADDING) {
    __CPROVER_assert(fr.padding.len == (size_t)rv, "padding len");
  }
}
