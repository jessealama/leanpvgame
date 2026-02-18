import Game.Levels.TheGrinder.L05_Pattern

World "TheGrinder"
Level 6

Title "Victory: The Full Grinder"

Introduction "
All grind annotations are in scope through the import chain:
- `@[grind =] double_eq` — rewrites `double n` to `n + n`
- `@[grind →] double_pos` — derives `0 < double n` from `0 < n`
- `@[grind] myMap_len_eq` — instantiates `(myMap f l).length = l.length`

**The challenge**: prove a conjunction using all three engines.

```lean
grinder_victory (f : Nat → Nat) (n : Nat) (h : 0 < n) :
    (myMap f [n, double n]).length = 2 ∧ 0 < double n
```

- **Right conjunct** `0 < double n`: `@[grind →] double_pos` fires on `h : 0 < n`. ✓
- **Left conjunct** `(myMap f [n, double n]).length = 2`:
  The `@[simp]` lemmas from World 3 unfold `myMap` and evaluate the list length to 2.
  Plain `simp` closes this part.

Use `constructor` to split the conjunction, then apply the right tool to each part.
"

/-- The full grinder: length + positivity in one shot -/
TheoremDoc grinder_victory as "grinder_victory"

Statement grinder_victory (f : Nat → Nat) (n : Nat) (h : 0 < n) :
    (myMap f [n, double n]).length = 2 ∧ 0 < double n := by
  Hint "Split with `constructor`. For the length goal, use `simp` — the `@[simp]`
  lemmas from World 3 (`myMap_cons`, `myMap_nil`) evaluate the list automatically.
  For the positivity goal, use `grind` — it fires the `@[grind →]` annotation."
  constructor
  · simp
  · grind

Conclusion "
You've mastered The Grinder!

**What you learned:**

- **`grind` alone** — congruence closure + linear arithmetic, no hints needed
- **`@[grind =]`** — equation rewriting: replaces `grind [def]` hints permanently
- **`@[grind →]`** — forward reasoning: chain implications about your functions
- **`@[grind]`** — E-matching: instantiate universally quantified lemmas automatically

**The workflow**: annotate your invariants and equations once; let `grind` verify
any downstream consequence — in this file, in future files, forever.

This is how industrial verification tools work: the specification is annotated once,
and the verifier checks every contract automatically.
"
