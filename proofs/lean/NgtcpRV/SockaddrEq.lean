/-!
# conn.c socket-address equality `ngtcp2_sockaddr_eq` (lib/ngtcp2_addr.c)

```c
  if (a->sa_family != b->sa_family) return 0;
  case AF_INET:  return port == port && memcmp(addr, addr, 4) == 0;
  case AF_INET6: return port == port && memcmp(addr6, addr6, 16) == 0;
```

This is the base comparison under `ngtcp2_addr_eq` / `ngtcp2_path_eq`.  We model a socket
address as either IPv4 (port + 32-bit address) or IPv6 (port + 128-bit address) and prove
`sockaddr_eq` matches structural identity, is an equivalence relation, and reports unequal
whenever the address families differ — so address matching is consistent.
-/
namespace NgtcpRV.SockaddrEq

/-- A socket address (address bytes abstracted as a value, matching `memcmp`). -/
inductive Sockaddr
  | inet (port : Nat) (addr : Nat)
  | inet6 (port : Nat) (addr : Nat)
  deriving DecidableEq, Repr

open Sockaddr

/-- `ngtcp2_sockaddr_eq`. -/
def saEq : Sockaddr → Sockaddr → Bool
  | inet p1 a1, inet p2 a2 => (p1 == p2) && (a1 == a2)
  | inet6 p1 a1, inet6 p2 a2 => (p1 == p2) && (a1 == a2)
  | _, _ => false

/-- `sockaddr_eq` holds exactly when the addresses are structurally equal. -/
theorem saEq_iff (a b : Sockaddr) : saEq a b = true ↔ a = b := by
  cases a <;> cases b <;>
    simp [saEq] <;> constructor <;> intro h <;> (try exact ⟨h.1, h.2⟩) <;> (try omega) <;>
    (first | (obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl) | (injection h with h1 h2; exact ⟨h1, h2⟩))

/-- Reflexive. -/
theorem saEq_refl (a : Sockaddr) : saEq a a = true := by rw [saEq_iff]

/-- Symmetric. -/
theorem saEq_symm (a b : Sockaddr) (h : saEq a b = true) : saEq b a = true := by
  rw [saEq_iff] at h ⊢; exact h.symm

/-- Transitive. -/
theorem saEq_trans (a b c : Sockaddr) (h1 : saEq a b = true) (h2 : saEq b c = true) :
    saEq a c = true := by rw [saEq_iff] at h1 h2 ⊢; exact h1.trans h2

/-- Different address families are never equal. -/
theorem family_mismatch_v4v6 (p1 a1 p2 a2 : Nat) : saEq (inet p1 a1) (inet6 p2 a2) = false := rfl
theorem family_mismatch_v6v4 (p1 a1 p2 a2 : Nat) : saEq (inet6 p1 a1) (inet p2 a2) = false := rfl

end NgtcpRV.SockaddrEq
