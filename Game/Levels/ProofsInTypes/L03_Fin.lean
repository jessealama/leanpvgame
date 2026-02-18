import Game.Levels.ProofsInTypes.L02_SubtypeAccess

World "ProofsInTypes"
Level 3

Title "Fin n: Bounded Naturals"

Introduction "
`Fin n` is Lean's built-in type of natural numbers **strictly less than `n`**.
It's a subtype with two fields:
- `.val : Nat` — the number
- `.isLt : val < n` — the proof it's in bounds

```lean
-- This compiles: 3 < 5
example : Fin 5 := ⟨3, by omega⟩

-- This is a type error: 7 < 5 is false
-- example : Fin 5 := ⟨7, by omega⟩  -- omega can't prove 7 < 5
```

Array indexing with `Fin` is **always safe** — no runtime bounds check, no `Option`,
no panic. The bound is verified once, at compile time.
"

/-- For any `i : Fin n`, `i.val < n` -/
TheoremDoc fin_bound as "fin_bound"

Statement fin_bound : ∀ (n : Nat) (i : Fin n), i.val < n := by
  Hint "Every `Fin n` carries a proof field. Can you name it? Try `exact i.isLt`."
  intro n i; exact i.isLt

Conclusion "
`i.isLt` is always there, always valid. That's the promise of `Fin`.
"

/-- Type of natural numbers strictly less than `n`, bundled with the proof. -/
DefinitionDoc Fin as "Fin"
NewDefinition Fin
