#include <stdio.h>
#include "ngtcp2_pkt.h"
int main(void) {
  int64_t r = ngtcp2_pkt_adjust_pkt_num(4611686018427387902LL, 1006690231LL, 4);
  printf("returned %lld (max %lld)\n", (long long)r, (long long)NGTCP2_MAX_PKT_NUM);
  return 0;
}
