import Game.Levels.ProofsInTypes.L04_SafeHead

World "ProofsInTypes"
Level 5

Title "Sorted: An Inductive Predicate"

Introduction "
A **predicate on lists** can encode an invariant. Here is `Sorted` for `List Nat`:

```lean
@[simp] def Sorted : List Nat → Prop
  | []          => True
  | [_]         => True
  | x :: y :: ys => x ≤ y ∧ Sorted (y :: ys)
```

- An empty list is trivially sorted.
- A singleton list is trivially sorted.
- A list `x :: y :: ys` is sorted iff `x ≤ y` and `y :: ys` is sorted.

The tactic `simp [Sorted] at h` unfolds the predicate **inside a hypothesis**.
After `simp [Sorted] at h` where `h : Sorted (x :: y :: ys)`,
the hypothesis becomes `h : x ≤ y ∧ Sorted (y :: ys)`.
Then `.1` extracts the left part of `∧`.
"

@[simp] def Sorted : List Nat → Prop
  | []          => True
  | [_]         => True
  | x :: y :: ys => x ≤ y ∧ Sorted (y :: ys)

/-- If `Sorted (x :: y :: ys)`, then `x ≤ y` -/
TheoremDoc sorted_head_le as "sorted_head_le"

Statement sorted_head_le : ∀ (x y : Nat) (ys : List Nat),
    Sorted (x :: y :: ys) → x ≤ y := by
  Hint "`simp [Sorted] at h` unfolds the predicate in hypothesis `h`. Then `.1` extracts the left part of `∧`."
  intro x y ys h
  simp [Sorted] at h
  exact h.1

Conclusion "
`simp ... at h` is the variant that simplifies *hypotheses* rather than the goal.
It's essential when you need to unfold a definition to extract information from an assumption.
"

-- simp ... at h is just simp (already in inventory) applied to a hypothesis
/-- Predicate: a list of `Nat` is sorted in non-decreasing order. -/
DefinitionDoc Sorted as "Sorted"
NewDefinition Sorted
