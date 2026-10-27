/* ngtcp2_pkt_hd_init: copies dcid/scid structs (or zeros them) and sets fields;
   no UB for valid CID lengths, both the non-NULL and NULL paths. */
#include "ngtcp2_pkt.h"
void harness(void) {
  ngtcp2_pkt_hd hd;
  ngtcp2_cid dcid, scid;
  __CPROVER_assume(dcid.datalen <= NGTCP2_MAX_CIDLEN && scid.datalen <= NGTCP2_MAX_CIDLEN);
  uint8_t flags, type; int64_t pn; size_t pnl; uint32_t v;
  unsigned which; __CPROVER_assume(which < 2);
  if (which == 0) ngtcp2_pkt_hd_init(&hd, flags, type, &dcid, &scid, pn, pnl, v);
  else ngtcp2_pkt_hd_init(&hd, flags, type, 0, 0, pn, pnl, v);
  __CPROVER_assert(1, "reached without UB");
}
