import Game.Levels.PurePrograms.L01_MyMap

World "PurePrograms"
Level 2

Title "Filtering a List"

Introduction "
`filter` keeps only the elements that satisfy a predicate (a function returning `Bool`).

```lean
def myFilter {α : Type} (p : α → Bool) : List α → List α
  | []      => []
  | x :: xs => if p x then x :: myFilter p xs else myFilter p xs
```

When `p x` is `true`, we keep `x`; otherwise we drop it.

**Your goal**: prove that filtering never makes a list longer.

*Hint*: After `simp [myFilter]`, use `split` to case-split on whether `p x` is true or false,
then finish with `simp_all` and `omega`.
"

def myFilter {α : Type} (p : α → Bool) : List α → List α
  | []      => []
  | x :: xs => if p x then x :: myFilter p xs else myFilter p xs

/-- `(myFilter p l).length ≤ l.length` -/
TheoremDoc filter_length_le as "filter_length_le"

Statement filter_length_le : ∀ {α : Type} (p : α → Bool) (l : List α),
    (myFilter p l).length ≤ l.length := by
  intro α p l
  induction l with
  | nil          => simp [myFilter]
  | cons x xs ih =>
    simp [myFilter]
    split <;> simp_all <;> omega

Conclusion "
`myFilter` can only shrink (or preserve) a list — it can never grow it.
Notice how `split` handled the `if` expression cleanly, letting `simp_all` and `omega`
close each branch.
"

NewTactic split simp_all
/-- Keep only elements satisfying a boolean predicate. -/
DefinitionDoc myFilter as "myFilter"
NewDefinition myFilter
