#include <stdlib.h>
#include "ngtcp2_map.h"
/* ngtcp2_map_find never reads keys/data/psl out of bounds: the start index is
   key>>(64-hashbits) in [0,tablesize) and probing wraps via &(tablesize-1), so
   every access is masked in range.  The Robin Hood invariant psl[i] <= tablesize
   bounds the probe loop. */
void harness(void) {
  size_t hashbits; __CPROVER_assume(hashbits >= 1 && hashbits <= 3);
  size_t ts = (size_t)1 << hashbits;
  uint8_t *psl = malloc(ts);
  ngtcp2_map_key_type *keys = malloc(ts * sizeof(ngtcp2_map_key_type));
  void **data = malloc(ts * sizeof(void *));
  __CPROVER_assume(psl && keys && data);
  for (size_t i = 0; i < ts; ++i) __CPROVER_assume(psl[i] <= ts);  /* max displacement */
  ngtcp2_map map;
  map.hashbits = hashbits;
  map.psl = psl; map.keys = keys; map.data = data;
  __CPROVER_assume(map.size >= 1 && map.size <= ts);
  ngtcp2_map_key_type key;
  (void)ngtcp2_map_find(&map, key);
  free(psl); free(keys); free(data);
}
