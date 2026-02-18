import Game.Levels.TheGrinder.L02_Arith

World "TheGrinder"
Level 3

Title "@[grind =]: Teaching grind to Rewrite"

Introduction "
In World 3 you proved `double_injective` with `grind [double]` — passing the
definition as a hint. This works, but every call site needs the hint.

**A better approach**: annotate the equation once with `@[grind =]`, and
bare `grind` rewrites automatically — forever, everywhere.

```lean
@[grind =] theorem double_eq (n : Nat) : double n = n + n := rfl
```

The `@[grind =]` attribute registers `double_eq` as a left-to-right rewrite rule
in grind's engine. Now whenever grind sees `double n`, it rewrites to `n + n`.

```lean
Statement double_mul2 (n : Nat) : double n = 2 * n
```

With `double_eq` annotated:
1. `grind` rewrites `double n` → `n + n`
2. `n + n = 2 * n` is linear arithmetic ✓

Compare: in World 3 you wrote `grind [double]`. Here, bare `grind` suffices.
The annotation is the investment — the payoff is zero-hint proofs.
"

@[grind =] theorem double_eq (n : Nat) : double n = n + n := rfl

/-- `double n = 2 * n` (proved with annotated grind) -/
TheoremDoc double_mul2 as "double_mul2"

Statement double_mul2 (n : Nat) : double n = 2 * n := by
  Hint "Just `grind`. The `@[grind =]` annotation replaces the `[double]` hint from World 3."
  grind

Conclusion "
`@[grind =]` turned `double_eq` into a permanent rewrite rule for `grind`.

The workflow:
1. Prove your equation theorem.
2. Tag it `@[grind =]`.
3. From then on, bare `grind` rewrites it automatically — no `grind [...]` hints needed.

This is the `@[simp]` workflow you learned in World 3, but for `grind`.
"

/-- `double n = n + n` (registered as a grind rewrite rule) -/
TheoremDoc double_eq as "double_eq"
NewTheorem double_eq
