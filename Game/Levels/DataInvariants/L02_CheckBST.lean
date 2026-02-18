import Game.Levels.DataInvariants.L01_IsBST

World "DataInvariants"
Level 2

Title "Checking a BST"

Introduction "
Let's verify that a concrete tree satisfies the BST invariant.

```
      3
     / \\
    1   5
```

This tree is `.node (.node .leaf 1 .leaf) 3 (.node .leaf 5 .leaf)`.

To show `IsBST` holds, `simp` unfolds all three predicates (since they are
marked `@[simp]`) and reduces everything to numeric comparisons like
`1 < 3` and `3 < 5`. Then `omega` closes the arithmetic.
"

/-- A concrete 3-node tree is a valid BST. -/
TheoremDoc isBST_example as "isBST_example"

Statement isBST_example :
    IsBST (.node (.node .leaf 1 .leaf) 3 (.node .leaf 5 .leaf)) := by
  Hint "`simp` unfolds `IsBST`, `AllLt`, and `AllGt` (all marked `@[simp]`),
  reduces the numeric comparisons `1 < 3` and `3 < 5`, and closes the goal."
  simp

Conclusion "
`simp` unfolded the predicates, eliminated `True` conjuncts, and closed the
numeric comparisons — all in one step.

For larger trees you'd need more work, but the structure is always the same:
unfold the predicates, check the bounds at each node.
"
