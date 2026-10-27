/-!
Version-negotiation downgrade protection (conn.c `select_preferred_version`).

When negotiating the QUIC version, ngtcp2 returns the first of its OWN preferred
versions that is either the peer's chosen version or appears in the peer's
available-versions list; otherwise it returns a fixed fallback (RFC 9368).  The
security property is downgrade protection: the selected version is always one the
local endpoint explicitly prefers, or the fallback — a peer cannot force a version
the local endpoint did not list.  We prove exactly that.
-/
namespace NgtcpRV.ConnVersionNeg
variable {V : Type} [DecidableEq V]

/-- The first preferred version that is compatible (matches chosen, or is offered). -/
def findCompatible (preferred available : List V) (chosen : V) : Option V :=
  preferred.find? (fun pv => pv = chosen ∨ pv ∈ available)

/-- `select_preferred_version`: a compatible preferred version, else the fallback. -/
def selectVersion (preferred available : List V) (chosen fallback : V) : V :=
  (findCompatible preferred available chosen).getD fallback

/-- **Downgrade protection**: the negotiated version is either one of the local
endpoint's preferred versions or the fallback — never an arbitrary peer-imposed
version. -/
theorem select_preferred_or_fallback (preferred available : List V) (chosen fallback : V) :
    selectVersion preferred available chosen fallback ∈ preferred ∨
    selectVersion preferred available chosen fallback = fallback := by
  unfold selectVersion findCompatible
  cases hf : preferred.find? (fun pv => pv = chosen ∨ pv ∈ available) with
  | none => right; simp [hf]
  | some v =>
    left
    simp only [Option.getD_some]
    exact List.mem_of_find?_eq_some hf

/-- When the result is a preferred version, it really was compatible (equal to the
chosen version, or present in the peer's available list). -/
theorem selected_is_compatible (preferred available : List V) (chosen fallback : V)
    (v : V) (hf : findCompatible preferred available chosen = some v) :
    v = chosen ∨ v ∈ available := by
  have := List.find?_some hf
  simpa using this

end NgtcpRV.ConnVersionNeg
