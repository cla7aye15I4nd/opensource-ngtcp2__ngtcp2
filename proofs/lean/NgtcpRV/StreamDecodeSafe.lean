/-!
# STREAM frame decoder: data-field spatial safety for every flag combination

`ngtcp2_pkt_decode_stream_frame` is the most structurally complex frame decoder:
the type byte carries OFF/LEN/FIN bits that control which fields are present, and
the trailing stream-data region is delimited two different ways:

  * LEN bit SET: an explicit `Length` varint `vi` precedes the data; the decoder
    checks `if (payloadlen - len < vi) return` (with `len` = bytes through that
    varint) and the data occupies `[len, len + vi)`.
  * LEN bit CLEAR: the data runs to the end of the payload, computed in the
    decode pass as `datalen = payloadlen - (p - payload)` — a `size_t`
    subtraction that must not underflow.

Both forms reduce to one invariant: let `c` be the byte offset where the data
region begins (`p - payload`, i.e. `len` in the LEN-set case).  Validation has
established `c ≤ payloadlen`.  We prove that for BOTH delimitation modes the data
field `[c, c + datalen)` lies within `[0, payloadlen)` and the trailing
subtraction never underflows — covering all flag combinations at once.
-/
namespace NgtcpRV.StreamDecodeSafe

/-- The decode state at the data field: `pl` = payloadlen, `c` = offset where the
data begins (= `p - payload`; equals `len` when LEN is set), `lenbit` = LEN flag,
`vi` = the declared Length varint (used only when `lenbit`). -/
structure St where
  pl : Nat
  c  : Nat
  lenbit : Bool
  vi : Nat

/-- Validation has shown the cursor never passed the buffer end. -/
def ConsumedValid (h : St) : Prop := h.c ≤ h.pl

/-- The stream data length, exactly as the C computes it in each mode. -/
def datalen (h : St) : Nat := if h.lenbit then h.vi else h.pl - h.c

/-- The decoder accepted: in LEN mode the `payloadlen - len < vi` check did NOT
fire; in no-LEN mode there is no further check. -/
def Accepts (h : St) : Prop := if h.lenbit then ¬ (h.pl - h.c < h.vi) else True

/-- **Spatial safety for every flag combination**: under validation and
acceptance, the data field `[c, c + datalen)` fits in `[0, payloadlen)` — its end
`c + datalen ≤ payloadlen`, and when nonempty its start `c < payloadlen`. The
no-LEN subtraction `payloadlen - c` therefore never underflows. -/
theorem stream_data_in_bounds (h : St) (hc : ConsumedValid h) (ha : Accepts h) :
    h.c + datalen h ≤ h.pl ∧ (1 ≤ datalen h → h.c < h.pl) := by
  unfold ConsumedValid at hc
  cases hb : h.lenbit with
  | true  => simp [Accepts, datalen, hb] at ha ⊢; omega
  | false => simp [Accepts, datalen, hb] at ha ⊢ <;> omega

/-- The final cursor matches the returned frame length `len` in both modes
(the `assert((size_t)(p - payload) == len)`): `c + datalen` is `c + vi` when LEN
is set and `payloadlen` when it is clear (where the C sets `len = payloadlen`). -/
theorem cursor_eq (h : St) (hc : ConsumedValid h) :
    h.c + datalen h = if h.lenbit then h.c + h.vi else h.pl := by
  unfold ConsumedValid at hc
  cases hb : h.lenbit with
  | true  => simp [datalen, hb]
  | false => simp [datalen, hb]; omega

end NgtcpRV.StreamDecodeSafe
