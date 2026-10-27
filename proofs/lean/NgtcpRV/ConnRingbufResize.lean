/-!
ngtcp2_ringbuf_resize bound (ringbuf.c).

`ngtcp2_ringbuf_resize(rb, len)` sets the element count to `len`, with the
precondition `assert(len <= rb->mask + 1)` — the new length must fit the
power-of-two capacity.  We prove that a resize respecting the assertion keeps the
ring length within capacity (the `ConnRingbuf`/`RingBuf` invariant).
-/
namespace NgtcpRV.ConnRingbufResize

/-- `ngtcp2_ringbuf_resize`: set the length to `newLen` (asserts `newLen <= cap`). -/
def resize (newLen cap : Nat) : Nat := newLen

/-- **Resize respects capacity**: with the assertion `newLen <= cap`, the resized
length is within the capacity. -/
theorem resize_within_cap (newLen cap : Nat) (h : newLen ≤ cap) :
    resize newLen cap ≤ cap := by unfold resize; exact h

end NgtcpRV.ConnRingbufResize
