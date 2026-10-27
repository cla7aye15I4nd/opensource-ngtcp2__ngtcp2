/-!
Big-endian uint16 / uint32 encode-decode roundtrip (conv.c `ngtcp2_put_uint16be`
/ `get_uint16be`, `put_uint32be` / `get_uint32be`).

`get16be` reads a 2-byte length field, `get32be` a 4-byte QUIC version; both must
recover exactly what `put*be` wrote.  We prove the value-level roundtrip for every
`uint16_t` and `uint32_t`.
-/
namespace NgtcpRV.ConvRoundtrip1632

def put16be (n : Nat) : List Nat := [n / 256 % 256, n % 256]
def get16be : List Nat → Nat
  | [b0, b1] => b0 * 256 + b1
  | _ => 0

theorem get_put16 (n : Nat) (h : n < 2 ^ 16) : get16be (put16be n) = n := by
  simp only [put16be, get16be]; omega

def put32be (n : Nat) : List Nat :=
  [n / 256^3 % 256, n / 256^2 % 256, n / 256^1 % 256, n / 256^0 % 256]
def get32be : List Nat → Nat
  | [b0, b1, b2, b3] => b0 * 256^3 + b1 * 256^2 + b2 * 256^1 + b3 * 256^0
  | _ => 0

theorem get_put32 (n : Nat) (h : n < 2 ^ 32) : get32be (put32be n) = n := by
  simp only [put32be, get32be]; omega

theorem put16be_length (n : Nat) : (put16be n).length = 2 := rfl
theorem put32be_length (n : Nat) : (put32be n).length = 4 := rfl

end NgtcpRV.ConvRoundtrip1632
