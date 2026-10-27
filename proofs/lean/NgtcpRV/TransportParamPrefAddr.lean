/-!
# Transport parameter PREFERRED_ADDRESS: staged-read spatial safety

`ngtcp2_transport_params_decode` handles the `preferred_address` parameter
(lib/ngtcp2_transport_params.c) with the subtlest read pattern in the function.
After reading the parameter's `valuelen` (and checking `end - p >= valuelen`), it
reads fields in STAGES around a length byte that it has not yet validated:

```c
  len = 4 + 2 + 16 + 2 + 1 + 16;                 /* = 41: addrs + cidlen byte + token */
  if (valuelen < len) return ERR;                /* valuelen >= 41 */
  ... read ipv4 addr(4)+port(2), ipv6 addr(16)+port(2)   /* 24 bytes */
  params->preferred_addr.cid.datalen = *p++;             /* 1 byte, offset 24 */
  len += cid.datalen;
  if (valuelen != len || cid.datalen > MAX_CIDLEN || cid.datalen < MIN_CIDLEN)
    return ERR;                                  /* valuelen == 41 + datalen, 1<=datalen<=20 */
  ... read cid.data(datalen), then stateless_reset_token(16)
```

The fixed 24 bytes and the length byte are read BEFORE the `valuelen == len` check;
the CID data and token are read AFTER.  Safety rests on the combination
`end - p >= valuelen` (checked up front) together with the exact-match
`valuelen == 41 + datalen`.  We prove every staged read lands within the available
bytes, and that total consumption equals `valuelen` exactly (the function's
closing `end - p != 0` accounting).
-/
namespace NgtcpRV.TransportParamPrefAddr

/-- Fixed address block: ipv4 addr(4)+port(2) + ipv6 addr(16)+port(2). -/
def FIXED_ADDR : Nat := 4 + 2 + 16 + 2
/-- stateless_reset_token length. -/
def TOKEN : Nat := 16
/-- `len` base = fixed addrs + the 1-byte cid length + token = 41. -/
def BASE : Nat := FIXED_ADDR + 1 + TOKEN
/-- `NGTCP2_MAX_CIDLEN`, the cid.data backing size. -/
def MAX_CIDLEN : Nat := 20

/-- Decode state at the parameter value: `avail = end - p` (checked `>= valuelen`),
the declared `valuelen`, and the CID length byte `datalen`. -/
structure Pre where
  avail : Nat
  valuelen : Nat
  datalen : Nat

/-- Everything the C has established by the time it begins the staged reads of the
CID data and token: `end - p >= valuelen`, `valuelen >= 41`, `1 <= datalen <= 20`,
and the exact-match `valuelen = 41 + datalen`. -/
def Valid (h : Pre) : Prop :=
  h.valuelen ≤ h.avail ∧ BASE ≤ h.valuelen ∧
  1 ≤ h.datalen ∧ h.datalen ≤ MAX_CIDLEN ∧ h.valuelen = BASE + h.datalen

/-- **Staged-read spatial safety**: under `Valid`, every read lands within the
`avail` bytes — the 24-byte fixed address block, the 1-byte CID length probe at
offset 24, the `datalen`-byte CID data, and the 16-byte token — and the total
bytes consumed equal `valuelen` exactly. -/
theorem prefaddr_reads_in_bounds (h : Pre) (hv : Valid h) :
    FIXED_ADDR ≤ h.avail ∧
    FIXED_ADDR + 1 ≤ h.avail ∧
    FIXED_ADDR + 1 + h.datalen ≤ h.avail ∧
    FIXED_ADDR + 1 + h.datalen + TOKEN ≤ h.avail ∧
    FIXED_ADDR + 1 + h.datalen + TOKEN = h.valuelen := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv
  unfold BASE FIXED_ADDR TOKEN at *
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- The CID data copy fits its backing array: `datalen <= NGTCP2_MAX_CIDLEN`. -/
theorem cid_fits (h : Pre) (hv : Valid h) : h.datalen ≤ MAX_CIDLEN := hv.2.2.2.1

end NgtcpRV.TransportParamPrefAddr
