import Game.Levels.AutomationPower.L04_MapAppend

World "AutomationPower"
Level 5

Title "Filter Partitions a List"

Introduction "
Let's do the same `@[simp]` treatment for `myFilter`, then prove a
new theorem about it.

```lean
@[simp] theorem myFilter_nil (p : α → Bool) :
    myFilter p [] = [] := rfl

@[simp] theorem myFilter_cons (p : α → Bool) (x : α) (xs : List α) :
    myFilter p (x :: xs) =
      if p x then x :: myFilter p xs else myFilter p xs := rfl
```

Now the theorem: filtering a list with a predicate `p` and filtering with
its complement `!p` together account for **every element**:
```lean
(myFilter p l).length + (myFilter (fun x => !p x) l).length = l.length
```

Each element goes into exactly one bucket — either `p` kept it or `!p` did.

The proof strategy:
- Induct on `l`
- For the `cons` case, case-split on `p x` with `cases h : p x`
- `simp_all` handles the filter simplification using `h`
- `omega` closes the arithmetic
"

@[simp] theorem myFilter_nil (p : α → Bool) : myFilter p [] = [] := rfl
@[simp] theorem myFilter_cons (p : α → Bool) (x : α) (xs : List α) :
    myFilter p (x :: xs) =
      if p x then x :: myFilter p xs else myFilter p xs := rfl

/-- `(myFilter p l).length + (myFilter (fun x => !p x) l).length = l.length` -/
TheoremDoc filter_partition as "filter_partition"

Statement filter_partition : ∀ {α : Type} (p : α → Bool) (l : List α),
    (myFilter p l).length + (myFilter (fun x => !p x) l).length = l.length := by
  Hint "Use `induction l`. The base case is `simp`.
  For `cons x xs ih`, try `cases h : p x <;> simp_all <;> omega`."
  intro α p l
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases h : p x <;> simp_all <;> omega

Conclusion "
`cases h : p x` splits on whether `p x = true` or `p x = false`,
naming the result `h` for use in subsequent tactics.

`simp_all` then:
- Unfolds `myFilter` on `x :: xs` using `h`
- Beta-reduces `(fun x => !p x) x` to `!p x`
- Simplifies `!true` or `!false` to resolve the complementary filter case

`omega` closes the remaining arithmetic (`k + (j+1) = 1+n` style goals).

With `@[simp]` on both `myMap` and `myFilter`, we're ready for the
grand finale.
"

/-- `myFilter p l` returns the sublist of `l` whose elements satisfy predicate `p`. -/
DefinitionDoc myFilter as "myFilter"
/-- `myFilter p [] = []` -/
TheoremDoc myFilter_nil as "myFilter_nil"
/-- `myFilter p (x :: xs) = if p x then x :: myFilter p xs else myFilter p xs` -/
TheoremDoc myFilter_cons as "myFilter_cons"
NewDefinition myFilter
NewTheorem myFilter_nil myFilter_cons
