/-!
Packet-number-space assignment (conn.c, RFC 9000 §12.3).

QUIC keeps three independent packet-number spaces — Initial (0), Handshake (1),
and Application/1-RTT (2) — and a packet's number is only ever compared within its
own space.  Each packet type maps to exactly one space: Initial → 0, Handshake →
1, 0-RTT and 1-RTT → 2 (they share the application space).  We prove this mapping
is total and lands in `{0,1,2}`, so spaces never alias and cross-space confusion
is impossible.
-/
namespace NgtcpRV.ConnPktNumSpace

inductive PktType where
  | initial | zeroRTT | handshake | oneRTT
deriving DecidableEq

/-- The packet-number space (0/1/2) a packet type belongs to. -/
def space : PktType → Nat
  | .initial   => 0
  | .handshake => 1
  | .zeroRTT   => 2
  | .oneRTT    => 2

/-- Every packet type maps to a valid space index `< 3`. -/
theorem space_valid (t : PktType) : space t < 3 := by
  cases t <;> decide

/-- 0-RTT and 1-RTT share the application packet-number space (so a 1-RTT ACK can
acknowledge 0-RTT packets); the other spaces are distinct. -/
theorem app_space_shared : space .zeroRTT = space .oneRTT := by decide

theorem spaces_distinct :
    space .initial ≠ space .handshake ∧
    space .initial ≠ space .oneRTT ∧
    space .handshake ≠ space .oneRTT := by decide

end NgtcpRV.ConnPktNumSpace
