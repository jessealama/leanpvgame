import Game.Levels.DataInvariants.L02_CheckBST

World "DataInvariants"
Level 3

Title "Inserting into an Empty Tree"

Introduction "
Does `bstInsert` preserve the BST property? Let's start with the simplest case:
inserting into an empty tree.

Recall:
```lean
bstInsert x .leaf = .node .leaf x .leaf
```

A single-node tree with empty subtrees is always a valid BST — both `AllLt`
and `AllGt` hold vacuously on leaves.
"

/-- Inserting into an empty tree yields a valid BST. -/
TheoremDoc isBST_insert_leaf as "isBST_insert_leaf"

Statement isBST_insert_leaf (x : Nat) : IsBST (bstInsert x .leaf) := by
  Hint "`simp [bstInsert]` unfolds the insertion into a leaf, giving `.node .leaf x .leaf`.
  Since all subtrees are leaves, the `IsBST` conditions reduce to `True`."
  simp [bstInsert]

Conclusion "
A single-node tree is trivially a BST — both subtrees are leaves, so `AllLt`
and `AllGt` hold vacuously.

The real challenge: preserving the invariant when inserting into a *non-empty* tree.
That requires showing the **bound predicates** `AllLt` and `AllGt` survive insertion.
"
