import Game.Levels.Termination.L04_Log2Double

World "Termination"
Level 5

Title "Sorted Merge Preserves Length"

Introduction "
The classic merge function from merge sort:

```lean
def merge (xs ys : List Nat) : List Nat :=
  match xs, ys with
  | [], ys       => ys
  | xs, []       => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys
termination_by xs.length + ys.length
decreasing_by all_goals (simp_wf; omega)
```

Neither `xs` nor `ys` alone decreases at every call — but their *combined*
length does. In the `x ≤ y` branch, `xs` shrinks; in the `else` branch, `ys`
shrinks. So `xs.length + ys.length` strictly decreases.

Four helper theorems are available:
```lean
merge_nil_left  : merge [] ys = ys
merge_nil_right : merge xs [] = xs
merge_cons_le   : x ≤ y → merge (x :: xs) (y :: ys) = x :: merge xs (y :: ys)
merge_cons_gt   : ¬x ≤ y → merge (x :: xs) (y :: ys) = y :: merge (x :: xs) ys
```

Prove that merging preserves the total number of elements.
"

def merge (xs ys : List Nat) : List Nat :=
  match xs, ys with
  | [], ys       => ys
  | xs, []       => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys
termination_by xs.length + ys.length
decreasing_by all_goals simp_wf

@[simp] theorem merge_nil_left (ys : List Nat) : merge [] ys = ys := by simp [merge]

@[simp] theorem merge_nil_right (xs : List Nat) : merge xs [] = xs := by
  cases xs <;> simp [merge]

@[simp] theorem merge_cons_le (x y : Nat) (xs ys : List Nat) (h : x ≤ y) :
    merge (x :: xs) (y :: ys) = x :: merge xs (y :: ys) := by
  simp [merge, h]

@[simp] theorem merge_cons_gt (x y : Nat) (xs ys : List Nat) (h : ¬x ≤ y) :
    merge (x :: xs) (y :: ys) = y :: merge (x :: xs) ys := by
  simp [merge, h]

/-- Merging two lists preserves the total number of elements. -/
TheoremDoc merge_length as "merge_length"

Statement merge_length (xs ys : List Nat) :
    (merge xs ys).length = xs.length + ys.length := by
  Hint "Use `induction xs generalizing ys` to split on the first list while keeping the IH general."
  induction xs generalizing ys with
  | nil => simp
  | cons x xs' ihxs =>
    Hint "Now use `induction ys` to split on the second list."
    induction ys with
    | nil => simp
    | cons y ys' ihys =>
      Hint "Use `by_cases h : x ≤ y` to split on which element goes first."
      by_cases h : x ≤ y
      · Hint "In the `x ≤ y` branch: `simp [h, ihxs]` then `omega`."
        simp [h, ihxs]; omega
      · Hint "In the `¬x ≤ y` branch: `have key := merge_cons_gt x y xs' ys' h`, then `simp [key, ihys]` and `omega`."
        have key := merge_cons_gt x y xs' ys' h
        simp [key, ihys]; omega

Conclusion "
The proof mirrors the termination argument exactly:
- Base cases (`nil` on either side) are immediate.
- In the recursive case, `by_cases h : x ≤ y` splits on which branch `merge` takes.
- `ihxs` gives the length fact for the `xs` branch; `ihys` for the `ys` branch.
- `omega` handles the arithmetic `1 + ... = ...` in each case.

This is the power of well-founded recursion: once Lean accepts the measure, the
function behaves like any total function in proofs.
"

/-- Sorted merge of two lists. -/
DefinitionDoc merge as "merge"
NewDefinition merge
/-- `merge [] ys = ys`. -/
TheoremDoc merge_nil_left as "merge_nil_left"

/-- `merge xs [] = xs`. -/
TheoremDoc merge_nil_right as "merge_nil_right"

/-- `x ≤ y → merge (x :: xs) (y :: ys) = x :: merge xs (y :: ys)`. -/
TheoremDoc merge_cons_le as "merge_cons_le"

/-- `¬x ≤ y → merge (x :: xs) (y :: ys) = y :: merge (x :: xs) ys`. -/
TheoremDoc merge_cons_gt as "merge_cons_gt"

NewTheorem merge_nil_left merge_nil_right merge_cons_le merge_cons_gt merge_length
