import Game.Levels.AutomationPower.L06_GrindBST

World "AutomationPower"
Level 7

Title "Filter-Map Fusion"

Introduction "
The payoff level. This theorem appears in compilers, query optimizers, and
functional programming textbooks: **filter-map fusion**.

```lean
myFilter p (myMap f l) = myMap f (myFilter (p ∘ f) l)
```

Filtering after mapping equals mapping after filtering with a composed
predicate. Instead of building an intermediate list (`myMap f l`) and then
filtering it, you can filter the *original* list by the composed predicate
`p ∘ f` and map only the elements that pass.

Without our automation tools, this would take 6+ manual lines. With
`@[simp]` on both `myMap` and `myFilter`, and `simp_all` finding the IH:

```lean
induction l with
| nil => simp
| cons x xs ih =>
  simp only [myMap_cons, myFilter_cons]
  cases h : p (f x) <;> simp_all [Function.comp_apply]
```

- `simp only [myMap_cons, myFilter_cons]` expands both sides one step.
- `cases h : p (f x)` splits on whether the element passes the filter.
- `simp_all [Function.comp_apply]` connects `(p ∘ f) x` to `p (f x)`,
  simplifies the `if` branches, and uses the IH.
"

/-- `myFilter p (myMap f l) = myMap f (myFilter (p ∘ f) l)` -/
TheoremDoc filter_map_fusion as "filter_map_fusion"

Statement filter_map_fusion : ∀ {α β : Type} (p : β → Bool) (f : α → β) (l : List α),
    myFilter p (myMap f l) = myMap f (myFilter (p ∘ f) l) := by
  Hint "Induct on `l`. For the `cons` case:
  `simp only [myMap_cons, myFilter_cons]`, then
  `cases h : p (f x) <;> simp_all [Function.comp_apply]`."
  intro α β p f l
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [myMap_cons, myFilter_cons]
    cases h : p (f x) <;> simp_all [Function.comp_apply]

Conclusion "
You've completed **World 3: Automation Power**!

The `@[simp]` investment made both the filter and map cases automatic.
`cases h : p (f x)` split the proof cleanly, and `simp_all [Function.comp_apply]`
tied together `(p ∘ f) x = p (f x)`, the filter branches, and the IH.

What you've mastered:
- **`simp_all`**: simplifies goals *and* hypotheses; IH is automatic
- **`@[simp]`**: tag your equations once, benefit everywhere
- **`grind`**: equality reasoning + arithmetic in one call
- **`cases h : expr`**: case-split and name the result for `simp_all`

These tools will power every world that follows.
"
