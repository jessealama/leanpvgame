import Game.Levels.PurePrograms.L05_Tree

World "PurePrograms"
Level 6

Title "Binary Search Tree"

Introduction "
A **Binary Search Tree (BST)** stores values in sorted order so we can search in
O(log n) time. The key property: every value in the left subtree is smaller than
the node's value, and every value in the right subtree is larger.

```lean
def bstInsert (x : Nat) : Tree Nat → Tree Nat
  | .leaf       => .node .leaf x .leaf
  | .node l y r =>
    if x < y then .node (bstInsert x l) y r
    else if y < x then .node l y (bstInsert x r)
    else .node l y r   -- x = y: already present

def bstMember (x : Nat) : Tree Nat → Bool
  | .leaf       => false
  | .node l y r =>
    if x < y then bstMember x l
    else if y < x then bstMember x r
    else true
```

**Your goal**: prove that after inserting `x`, searching for `x` always returns `true`.

*Hint*: Use `induction t`. For the `leaf` case, `simp [bstInsert, bstMember]` closes it.
For the `node` case, use `simp only [bstInsert]` to unfold the insert, then
`by_cases h : x < y` to split on the comparison, and close each branch with
`simp [h, bstMember, ...]`.
"

def bstInsert (x : Nat) : Tree Nat → Tree Nat
  | .leaf       => .node .leaf x .leaf
  | .node l y r =>
    if x < y then .node (bstInsert x l) y r
    else if y < x then .node l y (bstInsert x r)
    else .node l y r

def bstMember (x : Nat) : Tree Nat → Bool
  | .leaf       => false
  | .node l y r =>
    if x < y then bstMember x l
    else if y < x then bstMember x r
    else true

/-- `bstMember x (bstInsert x t) = true` -/
TheoremDoc member_after_insert as "member_after_insert"

Statement member_after_insert : ∀ (x : Nat) (t : Tree Nat),
    bstMember x (bstInsert x t) = true := by
  intro x t
  induction t with
  | leaf          => simp [bstInsert, bstMember]
  | node l y r ihl ihr =>
    simp only [bstInsert]
    by_cases h1 : x < y
    · simp [h1, bstMember, ihl]
    · by_cases h2 : y < x
      · simp [h1, h2, bstMember, ihr]
      · simp [h1, h2, bstMember]

Conclusion "
`bstMember x (bstInsert x t) = true` for all `x` and `t`.

This is the fundamental correctness property of BSTs: if you insert something,
you can always find it. Proving the full BST ordering invariant is left for World 5!
"

NewTactic by_cases
/-- Insert a value into a BST. -/
DefinitionDoc bstInsert as "bstInsert"
/-- Search for a value in a BST. -/
DefinitionDoc bstMember as "bstMember"
NewDefinition bstInsert bstMember
