import Game.Levels.TheGrinder.L03_GrindEq

World "TheGrinder"
Level 4

Title "@[grind →]: Forward Reasoning"

Introduction "
`@[grind =]` taught grind to rewrite equations. Now meet `@[grind →]`:
annotate an implication and grind applies it **automatically as a forward rule**.

A forward rule says: whenever the premise holds in context, add the conclusion.

```lean
@[grind →] theorem double_pos (n : Nat) (h : 0 < n) : 0 < double n := by
  simp [double]; omega
```

With this annotation, whenever grind sees `0 < ?n` as a hypothesis, it fires
`double_pos` and adds `0 < double ?n` to its working set.

**The challenge**: prove that `double` applied twice preserves positivity.

```lean
double_chain_pos (n : Nat) (h : 0 < n) : 0 < double (double n)
```

The chain:
1. `h : 0 < n` → fire `double_pos` → `0 < double n`
2. `0 < double n` → fire `double_pos` again → `0 < double (double n)` ✓

`omega` can't do this — it doesn't know `double`.
`simp` can't do this — it's not arithmetic simplification.
Only a forward rule engine can chain implications about defined functions.
"

@[grind →] theorem double_pos (n : Nat) (h : 0 < n) : 0 < double n := by
  simp [double]; omega

/-- `0 < n → 0 < double (double n)` -/
TheoremDoc double_chain_pos as "double_chain_pos"

Statement double_chain_pos (n : Nat) (h : 0 < n) : 0 < double (double n) := by
  Hint "Just `grind`. It applies `double_pos` twice: first to `n`, then to `double n`."
  grind

Conclusion "
`@[grind →]` registered `double_pos` as a forward inference rule.
`grind` fired it twice, chaining `0 < n → 0 < double n → 0 < double (double n)`.

The pattern generalizes: any implication `h₁ → h₂` about your functions can be
annotated `@[grind →]`, and grind will fire it automatically whenever `h₁` appears.
This enables **automated reasoning chains** — no manual `have` steps required.
"

/-- `0 < n → 0 < double n` (registered as a grind forward rule) -/
TheoremDoc double_pos as "double_pos"
NewTheorem double_pos
