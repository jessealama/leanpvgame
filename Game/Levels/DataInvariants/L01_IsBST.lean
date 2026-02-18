import Game.Levels.ProofsInTypes.L08_Victory
import Game.Levels.Termination.L06_Victory

World "DataInvariants"
Level 1

Title "The BST Invariant"

Introduction "
In World 2 you built binary search trees with `bstInsert` and proved
`bstMember x (bstInsert x t) = true`. But we never checked that `bstInsert`
actually **maintains** the BST ordering! A function might return `true` for
the wrong reasons if the tree's structure is broken.

Time to define what it **means** for a tree to be a valid BST.

Three predicates, all recursive on the tree:

```lean
@[simp] def AllLt (bound : Nat) : Tree Nat → Prop
  | .leaf => True
  | .node l x r => x < bound ∧ AllLt bound l ∧ AllLt bound r

@[simp] def AllGt (bound : Nat) : Tree Nat → Prop
  | .leaf => True
  | .node l x r => bound < x ∧ AllGt bound l ∧ AllGt bound r

@[simp] def IsBST : Tree Nat → Prop
  | .leaf => True
  | .node l x r => AllLt x l ∧ AllGt x r ∧ IsBST l ∧ IsBST r
```

- `AllLt bound t`: every value in `t` is strictly less than `bound`
- `AllGt bound t`: every value in `t` is strictly greater than `bound`
- `IsBST t`: left values < root < right values, recursively

An empty tree is trivially a BST. Prove it!
"

@[simp] def AllLt (bound : Nat) : Tree Nat → Prop
  | .leaf => True
  | .node l x r => x < bound ∧ AllLt bound l ∧ AllLt bound r

@[simp] def AllGt (bound : Nat) : Tree Nat → Prop
  | .leaf => True
  | .node l x r => bound < x ∧ AllGt bound l ∧ AllGt bound r

@[simp] def IsBST : Tree Nat → Prop
  | .leaf => True
  | .node l x r => AllLt x l ∧ AllGt x r ∧ IsBST l ∧ IsBST r

/-- An empty tree is a valid BST. -/
TheoremDoc isBST_leaf as "isBST_leaf"

Statement isBST_leaf : IsBST (.leaf : Tree Nat) := by
  Hint "`IsBST .leaf` unfolds to `True`. Use `simp` to close it."
  simp

Conclusion "
An empty tree is a BST — there are no elements to violate the ordering!

This is the base case for every BST proof. Next: checking a non-trivial tree.
"

/-- Every value in tree `t` is strictly less than `bound`. -/
DefinitionDoc AllLt as "AllLt"
/-- Every value in tree `t` is strictly greater than `bound`. -/
DefinitionDoc AllGt as "AllGt"
/-- A tree satisfies the BST ordering invariant. -/
DefinitionDoc IsBST as "IsBST"
NewDefinition AllLt AllGt IsBST
