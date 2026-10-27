/-!
Latency spin bit (conn.c, RFC 9000 §17.4).

The spin bit enables passive RTT measurement: a client sets the spin bit of its
outgoing 1-RTT packets to the OPPOSITE of the spin bit in the highest-numbered
packet it received; a server sets it to the SAME value.  This makes the spin bit
toggle exactly once per round trip.  We model the computation and prove the
client/server behaviour and that two consecutive client toggles restore the value
(one full RTT = two edges).
-/
namespace NgtcpRV.ConnSpinBit

/-- Outgoing spin bit from the received spin bit and the endpoint role. -/
def outSpin (recvSpin : Bool) (isClient : Bool) : Bool :=
  if isClient then !recvSpin else recvSpin

/-- A client flips the spin bit; a server echoes it. -/
theorem client_flips (b : Bool) : outSpin b true = !b := by unfold outSpin; simp
theorem server_echoes (b : Bool) : outSpin b false = b := by unfold outSpin; simp

/-- A full round trip (client flip composed with another client flip) restores the
spin value — the bit toggles once per RTT edge, twice per RTT. -/
theorem client_period_two (b : Bool) : outSpin (outSpin b true) true = b := by
  unfold outSpin; simp

end NgtcpRV.ConnSpinBit
