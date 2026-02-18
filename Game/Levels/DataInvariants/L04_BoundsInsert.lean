import Game.Levels.DataInvariants.L03_InsertLeaf

World "DataInvariants"
Level 4

Title "Bounds Survive Insertion"

Introduction "
The key to proving `bstInsert` preserves `IsBST` is showing that the
**bound predicates** `AllLt` and `AllGt` are preserved by insertion.

If every value in a tree is less than `bound`, and we insert `x < bound`,
then every value in the result is still less than `bound`.

The proof follows the structure of `bstInsert`: **induction** on the tree,
then **case-split** on `x < y` / `y < x` / `x = y`.

**Strategy**:
1. `induction t` — split into leaf and node cases
2. In the node case, `obtain` the pieces of `IsBST` and `AllLt`
3. `simp only [bstInsert]` to unfold the insertion one step
4. `by_cases hxy : x < y` to match `bstInsert`'s branching
5. In each branch, `simp` with the IH and hypotheses to close the goal
"

/-- If `AllLt bound t` and `x < bound` and `IsBST t`, then `AllLt bound (bstInsert x t)`. -/
TheoremDoc allLt_bstInsert as "allLt_bstInsert"

Statement allLt_bstInsert (x bound : Nat) (t : Tree Nat) :
    IsBST t → x < bound → AllLt bound t → AllLt bound (bstInsert x t) := by
  induction t with
  | leaf =>
    Hint "For the leaf case: `intro _ hx _` then `simp [bstInsert, hx]`."
    intro _ hx _
    simp [bstInsert, hx]
  | node l y r ihl ihr =>
    Hint "Introduce the hypotheses, then destructure them with `obtain`."
    intro hbst hx hbound
    simp only [IsBST] at hbst
    obtain ⟨hlt_l, hgt_r, hbst_l, hbst_r⟩ := hbst
    simp only [AllLt] at hbound
    obtain ⟨hy, hbl, hbr⟩ := hbound
    Hint "Now `simp only [bstInsert]` to unfold the insertion, then `by_cases hxy : x < y`."
    simp only [bstInsert]
    by_cases hxy : x < y
    · Hint "In this branch, `bstInsert` goes left. Use `simp` with the IH:
      `simp [hxy, hy, ihl hbst_l hx hbl, hbr]`."
      simp [hxy, hy, ihl hbst_l hx hbl, hbr]
    · by_cases hyx : y < x
      · Hint "`bstInsert` goes right. `simp [hxy, hyx, hy, hbl, ihr hbst_r hx hbr]`."
        simp [hxy, hyx, hy, hbl, ihr hbst_r hx hbr]
      · Hint "`x = y`, so the tree is unchanged. `simp [hxy, hyx, hy, hbl, hbr]`."
        simp [hxy, hyx, hy, hbl, hbr]

Conclusion "
The proof mirrors `bstInsert`'s structure exactly:

- **Leaf**: the single-node result has `x < bound` ✓
- **Node, x < y**: insert left; the IH gives `AllLt bound (bstInsert x l)`
- **Node, y < x**: insert right; the IH gives `AllLt bound (bstInsert x r)`
- **Node, x = y**: tree unchanged; original `AllLt bound t` still holds

This is the template for every invariant-preservation proof: **follow the operation's
structure** and show the invariant holds at each step.
"

NewTheorem allLt_bstInsert
