import Game.Metadata

World "PurePrograms"
Level 1

Title "Mapping Over a List"

Introduction "
In functional programming, `map` applies a function to every element of a list.
Let's define our own version and prove a key property about it.

```lean
def myMap {α β : Type} (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: myMap f xs
```

`myMap` takes a function `f : α → β` and a list of `α`s, returning a list of `β`s.
The output list has the same number of elements as the input.

**Your goal**: prove that `myMap` preserves the length of any list.

*Hint*: Use `induction` on the list, then `simp [myMap]` with the induction hypothesis.
"

def myMap {α β : Type} (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: myMap f xs

/-- `(myMap f l).length = l.length` -/
TheoremDoc map_length as "map_length"

Statement map_length : ∀ {α β : Type} (f : α → β) (l : List α),
    (myMap f l).length = l.length := by
  intro α β f l
  induction l with
  | nil          => simp [myMap]
  | cons x xs ih => simp [myMap, ih]

Conclusion "
Nice work! `myMap` always produces a list of the same length — regardless of what
function `f` does. This is a simple structural property that follows directly from
how the recursion is structured.
"

/-- Apply a function to every element of a list. -/
DefinitionDoc myMap as "myMap"
NewDefinition myMap
