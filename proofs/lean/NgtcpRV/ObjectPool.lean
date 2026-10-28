/-!
# conn.c object pool free-list `ngtcp2_opl` (lib/ngtcp2_opl.c)

```c
  void ngtcp2_opl_push(opl, ent) { ent->next = opl->head; opl->head = ent; }
  ngtcp2_opl_entry *ngtcp2_opl_pop(opl) {
    ent = opl->head; if (!ent) return NULL; opl->head = ent->next; return ent;
  }
  void ngtcp2_opl_clear(opl) { opl->head = NULL; }
```

The pool is a singly-linked LIFO free-list threaded through `ent->next`.  Modelling it as
the list of free entries (head at the front), we prove push/pop are a LIFO stack: popping
right after pushing returns exactly that entry and restores the pool, pop on an empty pool
yields NULL, and clear empties it.  This is the free-list's structural correctness — no
entry is lost or duplicated by a push/pop pair.
-/
namespace NgtcpRV.ObjectPool

variable {E : Type}

/-- `ngtcp2_opl_push`: prepend to the head. -/
def push (l : List E) (e : E) : List E := e :: l

/-- `ngtcp2_opl_pop`: remove the head (NULL when empty). -/
def pop : List E → Option E × List E
  | [] => (none, [])
  | x :: xs => (some x, xs)

/-- `ngtcp2_opl_clear`. -/
def clear (_ : List E) : List E := []

/-- **LIFO**: popping right after pushing returns that entry and restores the pool. -/
theorem pop_push (l : List E) (e : E) : pop (push l e) = (some e, l) := rfl

/-- Pop on an empty pool returns NULL and leaves it empty. -/
theorem pop_empty : pop ([] : List E) = (none, []) := rfl

/-- Clear empties the pool. -/
theorem clear_empty (l : List E) : clear l = [] := rfl

/-- Push increases the free count by one. -/
theorem push_length (l : List E) (e : E) : (push l e).length = l.length + 1 := rfl

/-- Pop on a nonempty pool decreases the free count by one (no entry lost or duplicated). -/
theorem pop_length (x : E) (xs : List E) : (pop (x :: xs)).2.length + 1 = (x :: xs).length := by
  simp [pop]

/-- A pushed entry is retrievable: the entry popped after a push equals what was pushed. -/
theorem push_pop_roundtrip (l : List E) (e : E) : (pop (push l e)).1 = some e := rfl

end NgtcpRV.ObjectPool
