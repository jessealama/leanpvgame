import Game.Levels.AutomationPower.L02_SimpAttr

World "AutomationPower"
Level 3

Title "grind: The Automated Prover"

Introduction "
`simp_all` is great for simplification. But some goals need more:
they require combining **equality reasoning** with **arithmetic**.

Enter **`grind`** — an automated prover that handles both at once.
`grind` performs *congruence closure* (equality reasoning) and integrates
linear arithmetic. Feed it lemmas with `grind [lemma, ...]` and it hunts
for a proof automatically.

Let's put `grind` to work on a new theorem from World 1 material.

You know `double n = n + n`. Now prove that `double` is **injective**:
if `double n = double m`, then `n = m`.

```lean
double_injective : ∀ (n m : Nat), double n = double m → n = m
```

Try `intro n m h; grind [double]`.
`grind [double]` tells the prover to use `double`'s definition as a rule.
It then rewrites `h : double n = double m` to `n + n = m + m` and deduces
`n = m` via arithmetic — all automatically.
"

/-- `double m = double n → m = n` -/
TheoremDoc double_injective as "double_injective"

Statement double_injective : ∀ (n m : Nat), double n = double m → n = m := by
  Hint "After `intro n m h`, try `grind [double]`.
  This tells `grind` to unfold `double` and then use arithmetic to finish."
  intro n m h
  grind [double]

Conclusion "
`grind [double]` unfolded the definition, rewrote the hypothesis, and
closed the goal with linear arithmetic — all in one call.

When `grind` needs a push, you can give it more lemma hints:
`grind [def1, lemma2, ...]`. Here, `[double]` was enough.

`grind` is particularly useful when you have hypotheses relating
computed values and need to derive new equalities or inequalities.
"

NewTactic grind
/-- `double n = n + n` -/
DefinitionDoc double as "double"
NewDefinition double
