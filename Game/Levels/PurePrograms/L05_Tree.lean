import Game.Levels.PurePrograms.L04_Half

World "PurePrograms"
Level 5

Title "Binary Trees"

Introduction "
Lists are one-dimensional. **Binary trees** branch in two directions:

```lean
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
```

A `Tree α` is either a `leaf` (empty) or a `node` with a left subtree, a value, and a right subtree.

We can measure a tree's height recursively:

```lean
def treeHeight : Tree α → Nat
  | .leaf       => 0
  | .node l _ r => 1 + max (treeHeight l) (treeHeight r)
```

Note: `treeHeight` is **structurally recursive** on `Tree α`, so Lean accepts it without
any `termination_by` annotation.

**Your goal**: prove that any non-empty tree (built with `node`) has height ≥ 1.
"

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α

def treeHeight : Tree α → Nat
  | .leaf       => 0
  | .node l _ r => 1 + max (treeHeight l) (treeHeight r)

/-- `treeHeight (node l x r) ≥ 1` -/
TheoremDoc height_node_pos as "height_node_pos"

Statement height_node_pos : ∀ {α : Type} (l r : Tree α) (x : α),
    treeHeight (.node l x r) ≥ 1 := by
  intro α l r x
  simp [treeHeight]

Conclusion "
Every `node` has height at least 1 — because we add 1 to the maximum of its children's heights.

Trees open the door to efficient data structures. In the next level, we'll build a
**Binary Search Tree** and prove its core correctness property.
"

/-- Binary tree type: either a leaf or a node with left subtree, value, right subtree. -/
DefinitionDoc Tree as "Tree"
/-- Height of a binary tree (0 for leaf, 1 + max of children for node). -/
DefinitionDoc treeHeight as "treeHeight"
NewDefinition Tree treeHeight
