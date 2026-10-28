/-!
# conn.c binary-heap index arithmetic `ngtcp2_pq` (lib/ngtcp2_pq.c)

`ngtcp2_pq` is a binary min-heap in an array: for a node at `index`,

```c
  parent = (index - 1) / 2;      /* bubble_up */
  j = index * 2 + 1;             /* left/right children in bubble_down: 2i+1, 2i+2 */
```

The heap's correctness and the termination of `bubble_up` / `bubble_down` rest on this
index arithmetic: the parent is strictly below a non-root node (so bubbling up reaches
the root), each child is strictly above its parent (so bubbling down reaches a leaf),
and the parent/child maps are mutual inverses (the array encodes a consistent tree).
We prove all of these.
-/
namespace NgtcpRV.PriorityQueue

/-- `parent(index) = (index - 1) / 2`. -/
def parent (i : Nat) : Nat := (i - 1) / 2
/-- Left child `2i + 1`. -/
def lchild (i : Nat) : Nat := i * 2 + 1
/-- Right child `2i + 2`. -/
def rchild (i : Nat) : Nat := i * 2 + 2

/-- **bubble_up terminates**: a non-root node's parent has a strictly smaller index. -/
theorem parent_lt (i : Nat) (h : 0 < i) : parent i < i := by unfold parent; omega

/-- **bubble_down descends (left)**: a left child has a strictly larger index than its parent. -/
theorem lt_lchild (i : Nat) : i < lchild i := by unfold lchild; omega
/-- **bubble_down descends (right)**: likewise for the right child. -/
theorem lt_rchild (i : Nat) : i < rchild i := by unfold rchild; omega

/-- The parent of a left child is the original node. -/
theorem parent_lchild (i : Nat) : parent (lchild i) = i := by unfold parent lchild; omega
/-- The parent of a right child is the original node. -/
theorem parent_rchild (i : Nat) : parent (rchild i) = i := by unfold parent rchild; omega

/-- The two children are distinct and consecutive. -/
theorem children_distinct (i : Nat) : lchild i + 1 = rchild i := by unfold lchild rchild; omega

/-- Heap-order index sanity: for any non-root `i`, `i` sits strictly between its parent
and each of its own children. -/
theorem index_between (i : Nat) (h : 0 < i) : parent i < i ∧ i < lchild i ∧ i < rchild i :=
  ⟨parent_lt i h, lt_lchild i, lt_rchild i⟩

end NgtcpRV.PriorityQueue
