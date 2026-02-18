import Game.Levels.AutomationPower.L05_FilterPartition

World "AutomationPower"
Level 6

Title "BST Insert: simp_all in Action"

Introduction "
In World 2, you proved BST correctness with explicit `simp [h1, h2, bstMember, ihl]` calls.
`simp_all` can improve this — but with a catch.

**The key insight**: `simp_all` works best with *positive* hypotheses like `h : x < y`.
It can search the context for `ihl` and `ihr` automatically. However, when you have
`h : ¬(x < y)`, `simp_all` normalizes it to `h : y ≤ x`, which prevents the standard
`if x < y then ... else ...` reduction. For those branches, plain `simp [h, ...]` is safer.

**World 2 proof**:
```lean
by_cases h1 : x < y
· simp [h1, bstMember, ihl]        -- explicit ihl needed
· by_cases h2 : y < x
  · simp [h1, h2, bstMember, ihr]  -- explicit ihr needed
  · simp [h1, h2, bstMember]
```

**World 3 proof** — `simp_all` handles the positive branch automatically:
```lean
by_cases h1 : x < y
· simp_all [bstMember]           -- finds ihl automatically ✓
· by_cases h2 : y < x
  · simp [bstMember, h1, h2, ihr]
  · simp [bstMember, h1, h2]
```

The first branch is now cleaner. The `simp_all` found `ihl` in the context without
being told. The other branches still use `simp` with explicit hints.
"

/-- `bstMember x (bstInsert x t) = true` for any `x` and tree `t`. -/
TheoremDoc bst_member_after_insert as "bst_member_after_insert"

Statement bst_member_after_insert : ∀ (x : Nat) (t : Tree Nat),
    bstMember x (bstInsert x t) = true := by
  Hint "Use `induction t`. For `leaf`, `simp [bstInsert, bstMember]` closes it.
  For `node l y r ihl ihr`: `simp only [bstInsert]`, then `by_cases h1 : x < y`.
  - If `h1 : x < y`: `simp_all [bstMember]` finds the IH automatically.
  - If `h1 : ¬(x < y)`: use a second `by_cases h2 : y < x` and `simp [bstMember, h1, h2, ...]`."
  intro x t
  induction t with
  | leaf => simp [bstInsert, bstMember]
  | node l y r ihl ihr =>
    simp only [bstInsert]
    by_cases h1 : x < y
    · simp_all [bstMember]
    · by_cases h2 : y < x
      · simp [bstMember, h1, h2, ihr]
      · simp [bstMember, h1, h2]

Conclusion "
`simp_all [bstMember]` in the first branch found the induction hypothesis `ihl`
without being told — it scanned the context and used it. That's one fewer explicit hint.

The negation branches still use `simp [h, ...]` because `simp_all` normalizes
`¬(x < y)` to `y ≤ x`, which can confuse the if-then-else reduction. Plain `simp [h]`
uses the hypothesis as-is, applying `if_neg h` directly.

**Takeaway**: `simp_all` is a powerful default, but knowing when to fall back to
`simp [explicit_hints]` is part of mastering Lean automation.
"

/-- A binary tree: either a leaf or a node with left subtree, value, and right subtree. -/
DefinitionDoc Tree as "Tree"
/-- Insert a value into a binary search tree, maintaining the BST ordering invariant. -/
DefinitionDoc bstInsert as "bstInsert"
/-- Test whether a value is a member of a binary search tree. -/
DefinitionDoc bstMember as "bstMember"
NewDefinition Tree bstInsert bstMember
