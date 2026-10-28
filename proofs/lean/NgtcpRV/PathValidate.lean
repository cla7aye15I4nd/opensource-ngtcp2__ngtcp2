/-!
# conn.c path validation: a path validates only by echoing a sent challenge

Eighth stateful conn.c subsystem.  `ngtcp2_pv_validate` (lib/ngtcp2_pv.c:95)
decides whether an incoming PATH_RESPONSE validates a path: it scans the stored
PATH_CHALLENGE entries and succeeds only if the response `data` equals the 8-byte
token of some entry it previously sent:

```c
  for (i = 0; i < len; ++i) {
    ent = ngtcp2_ringbuf_get(&pv->ents.rb, i);
    if (ngtcp2_cmemeq(ent->data.data, data->data, sizeof(ent->data.data))) {
      *pflags = ent->flags;
      return 0;                         // validated
    }
  }
  return NGTCP2_ERR_INVALID_ARGUMENT;    // no match
```
(empty entry list ⇒ `NGTCP2_ERR_INVALID_STATE`).

The security property (RFC 9000 §8.2): a path is validated **only** by returning a
token the endpoint actually chose and sent — an off-path attacker cannot validate a
path without observing or guessing the 64-bit challenge.  The entry store is a
fixed ring of `NGTCP2_PV_MAX_ENTRIES = 8`, bounding its memory.  We prove both.
-/
namespace NgtcpRV.PathValidate

/-- Max stored challenge entries (`NGTCP2_PV_MAX_ENTRIES`). -/
def MAX_ENTRIES : Nat := 8

/-- A stored PATH_CHALLENGE entry: its 64-bit token `data` and the `flags` reported
to the caller on a match. -/
structure Entry where
  data : Nat
  flags : Nat

/-- `ngtcp2_pv_validate`: the flags of the first entry whose token equals `data`,
or `none` (no match / empty store). -/
def validate (ents : List Entry) (data : Nat) : Option Nat :=
  (ents.find? (fun e => e.data == data)).map Entry.flags

/-- **Soundness / unforgeability**: if validation succeeds, some stored entry held
exactly this token — so a path is validated only by echoing a sent challenge. -/
theorem validate_sound (ents : List Entry) (data f : Nat) (h : validate ents data = some f) :
    ∃ e ∈ ents, e.data = data ∧ e.flags = f := by
  unfold validate at h
  rcases hop : ents.find? (fun e => e.data == data) with _ | e
  · rw [hop] at h; simp at h
  · rw [hop] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hmem := List.mem_of_find?_eq_some hop
    have hp := List.find?_some hop
    refine ⟨e, hmem, ?_, h⟩
    simpa using hp

/-- If no stored token matches, validation fails — no path validated without a
matching challenge. -/
theorem validate_requires_match (ents : List Entry) (data : Nat)
    (h : ∀ e ∈ ents, e.data ≠ data) : validate ents data = none := by
  unfold validate
  rcases hop : ents.find? (fun e => e.data == data) with _ | e
  · rw [hop]; rfl
  · have hmem := List.mem_of_find?_eq_some hop
    have hp := List.find?_some hop
    exact absurd (by simpa using hp) (h e hmem)

/-- An empty entry store never validates (`NGTCP2_ERR_INVALID_STATE`). -/
theorem validate_empty (data : Nat) : validate [] data = none := rfl

/-- Push a new challenge entry into the fixed-capacity ring: append when there is
room, otherwise drop the oldest (ring overwrite). -/
def addEntry (ents : List Entry) (e : Entry) : List Entry :=
  if ents.length < MAX_ENTRIES then ents ++ [e] else ents.drop 1 ++ [e]

/-- The entry store never exceeds `NGTCP2_PV_MAX_ENTRIES`. -/
theorem addEntry_bounded (ents : List Entry) (e : Entry) (h : ents.length ≤ MAX_ENTRIES) :
    (addEntry ents e).length ≤ MAX_ENTRIES := by
  unfold addEntry MAX_ENTRIES at *
  split
  · simp [List.length_append]; omega
  · simp only [List.length_append, List.length_drop, List.length_cons, List.length_nil]
    omega

/-- Over any sequence of pushes, the entry store stays within the cap. -/
theorem runAdd_bounded (ents : List Entry) (es : List Entry) (h : ents.length ≤ MAX_ENTRIES) :
    (es.foldl addEntry ents).length ≤ MAX_ENTRIES := by
  induction es generalizing ents with
  | nil => simpa using h
  | cons e es ih =>
    simp only [List.foldl_cons]
    exact ih (addEntry ents e) (addEntry_bounded ents e h)

end NgtcpRV.PathValidate
