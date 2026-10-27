/* Proof prelude: only what the extracted functions need. */
#include <stdint.h>
#include <stddef.h>
#define NGTCP2_MAX_VARINT ((1ULL << 62) - 1)
#define ngtcp2_ntohs(N) __builtin_bswap16(N)
#define ngtcp2_ntohl(N) __builtin_bswap32(N)
#define ngtcp2_htons(N) __builtin_bswap16(N)
#define ngtcp2_htonl(N) __builtin_bswap32(N)
#define ngtcp2_ntohl64(N) __builtin_bswap64(N)
#define ngtcp2_htonl64(N) __builtin_bswap64(N)
#define ngtcp2_unreachable() __builtin_trap()
#define ngtcp2_max(A, B) ((A) > (B) ? (A) : (B))
#define ngtcp2_min(A, B) ((A) < (B) ? (A) : (B))
#define memcpy __builtin_memcpy
/* Debug-build assert: a failed assertion traps (decodes to no instruction). */
#define assert(c) ((c) ? (void)0 : __builtin_trap())
typedef struct ngtcp2_range { uint64_t begin; uint64_t end; } ngtcp2_range;
static inline uint8_t *ngtcp2_cpymem(uint8_t *dest, const void *src, size_t n) {
  memcpy(dest, src, n); return dest + n; }
