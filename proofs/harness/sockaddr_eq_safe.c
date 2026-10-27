#include "ngtcp2_addr.h"
#include <ngtcp2/ngtcp2.h>
/* ngtcp2_sockaddr_eq: memory-safe and an equivalence (reflexive, symmetric)
   for both IPv4 and IPv6 addresses. */
void harness(void) {
  { ngtcp2_sockaddr_in6 a, b;
    a.sin6_family = NGTCP2_AF_INET6; b.sin6_family = NGTCP2_AF_INET6;
    ngtcp2_sockaddr *pa = (ngtcp2_sockaddr *)&a, *pb = (ngtcp2_sockaddr *)&b;
    __CPROVER_assert(ngtcp2_sockaddr_eq(pa, pa) == 1, "v6 reflexive");
    __CPROVER_assert(ngtcp2_sockaddr_eq(pa, pb) == ngtcp2_sockaddr_eq(pb, pa), "v6 symmetric"); }
  { ngtcp2_sockaddr_in a, b;
    a.sin_family = NGTCP2_AF_INET; b.sin_family = NGTCP2_AF_INET;
    ngtcp2_sockaddr *pa = (ngtcp2_sockaddr *)&a, *pb = (ngtcp2_sockaddr *)&b;
    __CPROVER_assert(ngtcp2_sockaddr_eq(pa, pa) == 1, "v4 reflexive");
    __CPROVER_assert(ngtcp2_sockaddr_eq(pa, pb) == ngtcp2_sockaddr_eq(pb, pa), "v4 symmetric"); }
}
