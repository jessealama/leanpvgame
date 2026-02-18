import Game.Levels.AutomationPower.L01_SimpAll

World "AutomationPower"
Level 2

Title "@[simp]: Teaching simp New Rules"

Introduction "
`simp` has a built-in library of rewrite rules. You can extend it permanently
by tagging your own theorems with the **`@[simp]` attribute**.

After marking a theorem `@[simp]`, plain `simp` (and `simp_all`) uses it
automatically — you never need to write `simp [myMap]` again.

The equation lemmas of `myMap` make great simp rules:
```lean
@[simp] theorem myMap_nil (f : α → β) :
    myMap f [] = [] := rfl

@[simp] theorem myMap_cons (f : α → β) (x : α) (xs : List α) :
    myMap f (x :: xs) = f x :: myMap f xs := rfl
```

Both are proved by `rfl` because they follow directly from `myMap`'s definition.

With these in place, `simp` knows how `myMap` behaves on every list shape.
Now prove a brand-new theorem: **`myMap` respects function composition**.

`myMap g (myMap f l) = myMap (g ∘ f) l`

Mapping `f` then `g` is the same as mapping their composition in one pass.
Try `induction l <;> simp_all [Function.comp_apply]`.
"

@[simp] theorem myMap_nil (f : α → β) : myMap f [] = [] := rfl
@[simp] theorem myMap_cons (f : α → β) (x : α) (xs : List α) :
    myMap f (x :: xs) = f x :: myMap f xs := rfl

/-- `myMap g (myMap f l) = myMap (g ∘ f) l` -/
TheoremDoc map_comp as "map_comp"

Statement map_comp : ∀ {α β γ : Type} (f : α → β) (g : β → γ) (l : List α),
    myMap g (myMap f l) = myMap (g ∘ f) l := by
  Hint "Use `induction l <;> simp_all [Function.comp_apply]`.
  `Function.comp_apply` is the lemma `(f ∘ g) x = f (g x)`.
  The `@[simp]` lemmas for `myMap` and the induction hypothesis do the rest."
  intro α β γ f g l
  induction l <;> simp_all [Function.comp_apply]

Conclusion "
`@[simp]` turned `myMap`'s equation lemmas into permanent simplification rules.
`simp_all` then used them (plus the IH) to close both the base and inductive cases
without any manual guidance.

This is the `@[simp]` workflow:
1. Tag your function's equations with `@[simp]`.
2. From then on, use plain `simp` or `simp_all` — no hints needed.
"

NewDefinition myMap
/-- `myMap f [] = []` -/
TheoremDoc myMap_nil as "myMap_nil"
/-- `myMap f (x :: xs) = f x :: myMap f xs` -/
TheoremDoc myMap_cons as "myMap_cons"
/-- `(f ∘ g) x = f (g x)` -/
TheoremDoc Function.comp_apply as "Function.comp_apply"
NewTheorem myMap_nil myMap_cons Function.comp_apply
