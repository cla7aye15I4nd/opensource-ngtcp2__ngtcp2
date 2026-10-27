/-!
Stateless-reset decode buffer safety (pkt.c `ngtcp2_pkt_decode_stateless_reset`).

A stateless reset is `randlen` unpredictable bytes followed by a 16-byte token.
The decoder first checks `payloadlen >= NGTCP2_MIN_STATELESS_RESET_RANDLEN (5) +
TOKENLEN (16)`; it then sets `randlen = payloadlen - 16` and reads the token from
`payload + randlen` for 16 bytes.  We prove the length check makes the `randlen`
subtraction underflow-free and the 16-byte token read `[randlen, payloadlen)`
stay inside the packet.
-/
namespace NgtcpRV.ConnStatelessReset

def MIN_RANDLEN : Nat := 5
def TOKENLEN : Nat := 16

/-- **Decode is in bounds**: with the validated length, `randlen = payloadlen - 16`
does not underflow, satisfies the minimum random length, and the token read
`[randlen, randlen + 16)` lies entirely within `[0, payloadlen)`. -/
theorem decode_safe (payloadlen : Nat) (h : MIN_RANDLEN + TOKENLEN ≤ payloadlen) :
    let randlen := payloadlen - TOKENLEN
    randlen + TOKENLEN = payloadlen ∧      -- no underflow; token read ends exactly at payloadlen
    MIN_RANDLEN ≤ randlen ∧                -- random part meets its minimum
    randlen + TOKENLEN ≤ payloadlen := by  -- token read in bounds
  simp only [MIN_RANDLEN, TOKENLEN] at *
  omega

/-- Every index the 16-byte token read touches is a valid packet offset. -/
theorem token_read_in_bounds (payloadlen i : Nat) (h : MIN_RANDLEN + TOKENLEN ≤ payloadlen)
    (hi : payloadlen - TOKENLEN ≤ i) (hi2 : i < payloadlen - TOKENLEN + TOKENLEN) :
    i < payloadlen := by
  simp only [MIN_RANDLEN, TOKENLEN] at *
  omega

end NgtcpRV.ConnStatelessReset
