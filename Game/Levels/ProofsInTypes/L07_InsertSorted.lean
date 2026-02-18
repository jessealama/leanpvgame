import Game.Levels.ProofsInTypes.L06_SortedList

World "ProofsInTypes"
Level 7

Title "insertSorted: Preserving the Invariant"

Introduction "
Having a `SortedList` type is only useful if we can **build** sorted lists.
Here is a function that inserts an element into a sorted list, keeping it sorted:

```lean
def insertSorted (x : Nat) : List Nat → List Nat
  | []      => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys
```

We need to prove that `insertSorted` **preserves** sortedness. The proof goes by
induction on the list. At each step we case-split on whether `x ≤ y`.

Key tactics:
- `by_cases hxy : x ≤ y` — split into two cases
- `simp only [if_pos hxy]` / `simp only [if_neg hxy]` — reduce the conditional
- `simp [Sorted]` — unfold the predicate and close the goal
"

def insertSorted (x : Nat) : List Nat → List Nat
  | []      => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

@[simp] theorem insertSorted_nil (x : Nat) :
    insertSorted x [] = [x] := rfl

@[simp] theorem insertSorted_cons_le (x y : Nat) (ys : List Nat) (h : x ≤ y) :
    insertSorted x (y :: ys) = x :: y :: ys := by simp [insertSorted, h]

@[simp] theorem insertSorted_cons_gt (x y : Nat) (ys : List Nat) (h : ¬x ≤ y) :
    insertSorted x (y :: ys) = y :: insertSorted x ys := by simp [insertSorted, h]

/-- Inserting into a sorted list yields a sorted list. -/
TheoremDoc insertSorted_sorted as "insertSorted_sorted"

Statement insertSorted_sorted : ∀ (x : Nat) (l : List Nat),
    Sorted l → Sorted (insertSorted x l) := by
  Hint "Induct on `l`. For the `cons` case, use `by_cases hxy : x ≤ y`.
  Then `simp only [if_pos hxy]` or `simp only [if_neg hxy]` to reduce the conditional,
  and `simp [Sorted]` to unfold the predicate."
  intro x l hs
  induction l with
  | nil => simp
  | cons y ys ih =>
    simp only [insertSorted]
    by_cases hxy : x ≤ y
    · simp only [if_pos hxy, Sorted]
      exact ⟨hxy, hs⟩
    · simp only [if_neg hxy]
      cases ys with
      | nil => simp [Sorted]; omega
      | cons z zs =>
        simp [Sorted] at hs
        have hih : Sorted (insertSorted x (z :: zs)) := ih hs.2
        by_cases hxz : x ≤ z
        · simp only [insertSorted_cons_le _ _ _ hxz] at hih ⊢
          simp [Sorted]; exact ⟨by omega, hih⟩
        · simp only [insertSorted_cons_gt _ _ _ hxz] at hih ⊢
          simp [Sorted]; exact ⟨hs.1, hih⟩

Conclusion "
Proved once, trusted forever. Any call to `insertSorted` on a sorted list yields
a sorted list — the compiler will hold us to this contract on every use.
"

/-- Insert a `Nat` into a sorted list, preserving order. -/
DefinitionDoc insertSorted as "insertSorted"
NewDefinition insertSorted
/-- `insertSorted x [] = [x]` -/
TheoremDoc insertSorted_nil as "insertSorted_nil"
/-- When `x ≤ y`: `insertSorted x (y :: ys) = x :: y :: ys` -/
TheoremDoc insertSorted_cons_le as "insertSorted_cons_le"
/-- When `¬(x ≤ y)`: `insertSorted x (y :: ys) = y :: insertSorted x ys` -/
TheoremDoc insertSorted_cons_gt as "insertSorted_cons_gt"
/-- If `¬p`, then `if p then a else b = b`. -/
TheoremDoc if_neg as "if_neg"
/-- If `p`, then `if p then a else b = a`. -/
TheoremDoc if_pos as "if_pos"
NewTheorem insertSorted_nil insertSorted_cons_le insertSorted_cons_gt if_neg if_pos
