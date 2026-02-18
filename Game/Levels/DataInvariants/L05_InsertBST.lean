import Game.Levels.DataInvariants.L04_BoundsInsert

World "DataInvariants"
Level 5

Title "Insert Preserves BST"

Introduction "
You proved that `AllLt` survives insertion. The symmetric result for `AllGt`
is provided below (the proof is identical with `<` flipped):

```lean
theorem allGt_bstInsert (x bound : Nat) (t : Tree Nat) :
    IsBST t → bound < x → AllGt bound t → AllGt bound (bstInsert x t)
```

Now prove the main theorem: **`bstInsert` preserves `IsBST`**.

The structure is the same as Level 4:
1. Induction on `t`, then destructure `IsBST` in the node case
2. Case-split on `x < y` / `y < x` / `x = y`
3. In each branch, assemble the four parts of `IsBST` for the result:
   - `AllLt y (...)` — use `allLt_bstInsert` when the left subtree changed
   - `AllGt y (...)` — use `allGt_bstInsert` when the right subtree changed
   - `IsBST (...)` — use the induction hypothesis for the changed subtree
   - The unchanged subtree keeps its original proof
"

-- Symmetric version of allLt_bstInsert (provided, not proved by player)
theorem allGt_bstInsert (x bound : Nat) (t : Tree Nat) :
    IsBST t → bound < x → AllGt bound t → AllGt bound (bstInsert x t) := by
  induction t with
  | leaf =>
    intro _ hx _
    simp [bstInsert, hx]
  | node l y r ihl ihr =>
    intro hbst hx hbound
    simp only [IsBST] at hbst
    obtain ⟨hlt_l, hgt_r, hbst_l, hbst_r⟩ := hbst
    simp only [AllGt] at hbound
    obtain ⟨hy, hbl, hbr⟩ := hbound
    simp only [bstInsert]
    by_cases hxy : x < y
    · simp [hxy, hy, ihl hbst_l hx hbl, hbr]
    · by_cases hyx : y < x
      · simp [hxy, hyx, hy, hbl, ihr hbst_r hx hbr]
      · simp [hxy, hyx, hy, hbl, hbr]

/-- Inserting into a BST yields a BST. -/
TheoremDoc isBST_bstInsert as "isBST_bstInsert"

Statement isBST_bstInsert (x : Nat) (t : Tree Nat) :
    IsBST t → IsBST (bstInsert x t) := by
  induction t with
  | leaf =>
    Hint "`intro _` then `simp [bstInsert]` — a single-node tree is a BST."
    intro _
    simp [bstInsert]
  | node l y r ihl ihr =>
    Hint "Introduce and destructure `IsBST (.node l y r)`:
    `intro hbst`
    `simp only [IsBST] at hbst`
    `obtain ⟨hlt_l, hgt_r, hbst_l, hbst_r⟩ := hbst`"
    intro hbst
    simp only [IsBST] at hbst
    obtain ⟨hlt_l, hgt_r, hbst_l, hbst_r⟩ := hbst
    simp only [bstInsert]
    Hint "Now `by_cases hxy : x < y` to match `bstInsert`'s branching."
    by_cases hxy : x < y
    · Hint "Insert went left. The result is `.node (bstInsert x l) y r`.
      Use `simp only [if_pos hxy, IsBST]` then
      `exact ⟨allLt_bstInsert x y l hbst_l hxy hlt_l, hgt_r, ihl hbst_l, hbst_r⟩`."
      simp only [if_pos hxy, IsBST]
      exact ⟨allLt_bstInsert x y l hbst_l hxy hlt_l, hgt_r, ihl hbst_l, hbst_r⟩
    · by_cases hyx : y < x
      · Hint "Insert went right. Use `allGt_bstInsert` for the right bound and `ihr` for `IsBST`."
        simp only [if_neg hxy, if_pos hyx, IsBST]
        exact ⟨hlt_l, allGt_bstInsert x y r hbst_r hyx hgt_r, hbst_l, ihr hbst_r⟩
      · Hint "`x = y`: tree unchanged. `simp only [if_neg hxy, if_neg hyx, IsBST]` then
        `exact ⟨hlt_l, hgt_r, hbst_l, hbst_r⟩`."
        simp only [if_neg hxy, if_neg hyx, IsBST]
        exact ⟨hlt_l, hgt_r, hbst_l, hbst_r⟩

Conclusion "
The crown jewel of this world: **`bstInsert` preserves `IsBST`**.

The proof assembled three ingredients:
- `allLt_bstInsert` — bounds on the left subtree survive insertion
- `allGt_bstInsert` — bounds on the right subtree survive insertion
- The induction hypothesis — `IsBST` on the modified subtree

This is the classic pattern for data-structure invariants: prove helpers for
each component, then combine them for the main theorem.
"

/-- If `AllGt bound t` and `bound < x` and `IsBST t`, then `AllGt bound (bstInsert x t)`. -/
TheoremDoc allGt_bstInsert as "allGt_bstInsert"
NewTheorem allGt_bstInsert isBST_bstInsert
