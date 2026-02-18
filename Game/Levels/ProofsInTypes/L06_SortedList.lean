import Game.Levels.ProofsInTypes.L05_Sorted

World "ProofsInTypes"
Level 6

Title "SortedList: A Type That IS Its Invariant"

Introduction "
We can pack the `Sorted` proof directly into a structure:

```lean
structure SortedList where
  data   : List Nat
  sorted : Sorted data
```

Now it is **impossible** to create an unsorted `SortedList`:

```lean
-- This is a type error — Sorted [3, 1, 2] requires 3 ≤ 1, which omega refutes
-- example : SortedList := ⟨[3, 1, 2], by simp [Sorted]; omega⟩
```

Compare to `List Nat + a separate boolean check`: the check might be bypassed,
forgotten, or tested only in some code paths. With `SortedList`, there is **no bypass**.

The empty sorted list is constructed with `trivial` for the `Sorted []` proof,
since `Sorted []` unfolds to `True`.
"

structure SortedList where
  data   : List Nat
  sorted : Sorted data

def emptySortedList : SortedList := ⟨[], trivial⟩

/-- The empty `SortedList` has `Sorted data`. -/
TheoremDoc empty_sorted as "empty_sorted"

Statement empty_sorted : Sorted emptySortedList.data := by
  Hint "The sorted proof is a struct field. Access it with `.sorted`."
  exact emptySortedList.sorted

Conclusion "
`SortedList` bakes the invariant into the type. You get correctness for free —
any function that takes a `SortedList` can trust it's sorted, no check needed.
"

/-- A list of `Nat` paired with a proof that it is sorted. -/
DefinitionDoc SortedList as "SortedList"
/-- The empty sorted list. -/
DefinitionDoc emptySortedList as "emptySortedList"
NewDefinition SortedList emptySortedList
