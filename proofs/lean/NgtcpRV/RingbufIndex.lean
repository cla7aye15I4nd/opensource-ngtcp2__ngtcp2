/-!
# ngtcp2_ringbuf: power-of-two index masking keeps every access in bounds

`ngtcp2_ringbuf` (lib/ngtcp2_ringbuf.c) backs the ACK tracker, path-validation
entries and the DCID store.  Its capacity is a power of two (`assert(ispow2(nmemb))`),
`mask = nmemb - 1`, and every physical index is computed by masking:

```c
  void *ngtcp2_ringbuf_get(rb, offset)   { offset = (rb->first + offset) & rb->mask; ... }
  void *ngtcp2_ringbuf_push_back(rb)     { offset = (rb->first + rb->len) & rb->mask; ... }
  rb->first = (rb->first + 1) & rb->mask;
```

Because `x & mask <= mask` for any `x`, every masked index is `<= mask`, i.e.
strictly below the capacity `mask + 1` — so ring accesses never go out of bounds,
regardless of how `first`/`len` evolve.  We also show the logical length invariant
`len <= capacity` is preserved by push_front / push_back.
-/
namespace NgtcpRV.RingbufIndex

/-- The physical buffer index `(first + offset) & mask`. -/
def physIdx (first offset mask : Nat) : Nat := (first + offset) &&& mask

/-- **Index in bounds**: a masked index never exceeds `mask`, hence is strictly less
than the capacity `mask + 1` — every ring access lands inside the buffer. -/
theorem phys_idx_le_mask (first offset mask : Nat) : physIdx first offset mask ≤ mask := by
  unfold physIdx; exact Nat.and_le_right

theorem phys_idx_lt_capacity (first offset mask : Nat) :
    physIdx first offset mask < mask + 1 := by
  have := phys_idx_le_mask first offset mask; omega

/-- The advanced `first` pointer `(first + 1) & mask` also stays within the ring. -/
theorem advanced_first_le_mask (first mask : Nat) : (first + 1) &&& mask ≤ mask :=
  Nat.and_le_right

/-- `push_back`: when full the length is held at capacity, otherwise incremented;
either way it stays within capacity. -/
def pushBackLen (len mask : Nat) : Nat := if len = mask + 1 then len else len + 1

/-- `push_front`: length incremented while below capacity. -/
def pushFrontLen (len mask : Nat) : Nat := if len < mask + 1 then len + 1 else len

/-- The capacity invariant `len <= mask + 1`. -/
def Inv (len mask : Nat) : Prop := len ≤ mask + 1

/-- `push_back` preserves `len <= capacity`. -/
theorem push_back_bounded (len mask : Nat) (h : Inv len mask) : Inv (pushBackLen len mask) mask := by
  unfold Inv pushBackLen at *; split <;> omega

/-- `push_front` preserves `len <= capacity`. -/
theorem push_front_bounded (len mask : Nat) (h : Inv len mask) : Inv (pushFrontLen len mask) mask := by
  unfold Inv pushFrontLen at *; split <;> omega

/-- A valid `get(offset)` (its precondition is `offset < len <= capacity`) therefore
reads a physical index strictly inside the buffer. -/
theorem get_in_bounds (first offset len mask : Nat)
    (hlen : Inv len mask) (hoff : offset < len) :
    physIdx first offset mask < mask + 1 := phys_idx_lt_capacity first offset mask

end NgtcpRV.RingbufIndex
