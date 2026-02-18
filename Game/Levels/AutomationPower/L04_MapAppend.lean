import Game.Levels.AutomationPower.L03_Grind

World "AutomationPower"
Level 4

Title "Map Distributes Over Append"

Introduction "
Now that `myMap`'s equations are tagged `@[simp]`, let's prove a new
structural theorem with almost no effort.

**`myMap` distributes over list concatenation**:
```lean
myMap f (l₁ ++ l₂) = myMap f l₁ ++ myMap f l₂
```

Mapping over a concatenated list is the same as mapping each part and
concatenating the results. This is the *functor* distributivity law.

In World 2, without `@[simp]` on `myMap`, you would have written:
```lean
induction l₁ with
| nil          => simp [myMap]
| cons x xs ih => simp [myMap, ih]
```

With `@[simp]` already in place, plain `simp_all` suffices — it knows
about `myMap` automatically and finds the IH in the context:
```lean
induction l₁ <;> simp_all
```

Try it!
"

/-- `myMap f (l₁ ++ l₂) = myMap f l₁ ++ myMap f l₂` -/
TheoremDoc map_append as "map_append"

Statement map_append : ∀ {α β : Type} (f : α → β) (l₁ l₂ : List α),
    myMap f (l₁ ++ l₂) = myMap f l₁ ++ myMap f l₂ := by
  Hint "Use `induction l₁ <;> simp_all`.
  The `@[simp]` lemmas for `myMap` from Level 2 fire automatically."
  intro α β f l₁ l₂
  induction l₁ <;> simp_all

Conclusion "
One line. The `@[simp]` investment in Level 2 pays off here.

`simp_all` sees `myMap_nil` and `myMap_cons` in the simp set, uses
the induction hypothesis from the context, and closes both cases.

This is the power of `@[simp]`: tag your equations once, benefit everywhere.
"
