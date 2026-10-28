/-!
# conn.c anti-amplification limit (RFC 9000 §8.1)

Before a path is validated, a server must not send more than three times the data
it has received from that address.  `dcid_tx_left` (lib/ngtcp2_conn.c:3112) returns
the remaining budget and asserts the invariant:

```c
  if (dcid->flags & NGTCP2_DCID_FLAG_PATH_VALIDATED) return SIZE_MAX;   /* no limit */
  assert(dcid->bytes_recv * 3 >= dcid->bytes_sent);
  return dcid->bytes_recv * 3 - dcid->bytes_sent;
```
and every server send is capped at this budget (`destlen = ngtcp2_min(destlen,
tx_left)`).  We model receives and (budget-capped) sends on an unvalidated path and
prove the anti-amplification invariant `bytes_sent ≤ 3 * bytes_recv` holds across
any sequence of events — so a spoofed-address peer cannot use the server as a
reflection amplifier — and that the `bytes_recv*3 - bytes_sent` subtraction never
underflows (the asserted precondition).
-/
namespace NgtcpRV.AmplificationLimit

structure Amp where
  bytesRecv : Nat
  bytesSent : Nat

/-- `dcid_tx_left` on an unvalidated path: the remaining 3x budget. -/
def txLeft (s : Amp) : Nat := 3 * s.bytesRecv - s.bytesSent

/-- The anti-amplification invariant. -/
def Inv (s : Amp) : Prop := s.bytesSent ≤ 3 * s.bytesRecv

inductive Op
  | recv (n : Nat)   -- received n bytes from the unvalidated address
  | send (k : Nat)   -- attempt to send k bytes; actually sends min(k, txLeft)

def apply (s : Amp) : Op → Amp
  | .recv n => { s with bytesRecv := s.bytesRecv + n }
  | .send k => { s with bytesSent := s.bytesSent + min k (txLeft s) }

/-- Every event preserves the anti-amplification invariant. -/
theorem apply_preserves (s : Amp) (op : Op) (h : Inv s) : Inv (apply s op) := by
  have hh : s.bytesSent ≤ 3 * s.bytesRecv := h
  cases op with
  | recv n => unfold apply Inv; dsimp only; omega
  | send k => unfold apply Inv txLeft; dsimp only; omega

/-- **tx_left underflow safety**: under the invariant the budget subtraction is
exact — `bytes_recv*3 - bytes_sent` never wraps (the asserted precondition). -/
theorem tx_left_no_underflow (s : Amp) (h : Inv s) :
    txLeft s + s.bytesSent = 3 * s.bytesRecv := by
  unfold txLeft; unfold Inv at h; omega

def run (s0 : Amp) (ops : List Op) : Amp := ops.foldl apply s0

/-- **Anti-amplification over any event sequence**: on an unvalidated path, total
bytes sent never exceed three times bytes received — no reflection amplification. -/
theorem run_inv (s0 : Amp) (ops : List Op) (h : Inv s0) : Inv (run s0 ops) := by
  unfold run
  induction ops generalizing s0 with
  | nil => simpa using h
  | cons op ops ih =>
    simp only [List.foldl_cons]
    exact ih (apply s0 op) (apply_preserves s0 op h)

/-- A budget-capped send never breaches the 3x limit, even applied directly. -/
theorem send_within_limit (s : Amp) (k : Nat) (h : Inv s) :
    (apply s (.send k)).bytesSent ≤ 3 * (apply s (.send k)).bytesRecv :=
  apply_preserves s (.send k) h

end NgtcpRV.AmplificationLimit
