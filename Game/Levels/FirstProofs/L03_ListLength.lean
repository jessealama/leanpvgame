import Game.Levels.FirstProofs.L02_IsEven

World "FirstProofs"
Level 3

Title "Length of Lists"

Introduction "Lists are everywhere in programming. Here's a fundamental property:
if you concatenate two lists, the length of the result is the sum of their lengths.
```
(xs ++ ys).length = xs.length + ys.length
```

Prove this for **all** lists `xs` and `ys` of natural numbers.

You'll need to reason by **structural induction** on the list `xs`:
- **Base case**: `xs = []` — the empty list is easy.
- **Inductive step**: `xs = x :: xs'` — use the *induction hypothesis* about `xs'`."

/-- `(xs ++ ys).length = xs.length + ys.length` -/
TheoremDoc append_length as "append_length"

Statement append_length : ∀ (xs ys : List Nat), (xs ++ ys).length = xs.length + ys.length := by
  Hint "Start with `intro xs ys`, then use `induction xs`."
  intro xs ys
  induction xs with
  | nil =>
    Hint "The empty list case: `simp` handles it."
    simp
  | cons x xs ih =>
    Hint "For `x :: xs`, try `simp [ih]` then `omega` for the arithmetic."
    simp [ih]
    omega

Conclusion "You proved a fundamental list theorem by structural induction!

The induction had two cases:
- **Base case** (`[]`): `([] ++ ys).length = ys.length = 0 + ys.length`, trivial.
- **Inductive case** (`x :: xs`): used the induction hypothesis `ih` and
  Lean's built-in list lemmas to reduce to arithmetic.

This is the essence of verification by induction."

NewTactic induction
