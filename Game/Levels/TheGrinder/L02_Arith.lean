import Game.Levels.TheGrinder.L01_Congr

World "TheGrinder"
Level 2

Title "Linear Arithmetic: Safety Conditions"

Introduction "
`grind` combines congruence closure with a built-in **linear arithmetic** solver —
think of it as `omega` integrated with the equality engine.

**The scenario**: you're writing bytes into a buffer of capacity `cap ≤ 1024`.
You've written `written` bytes and have `remaining` bytes left to write, with
`written + remaining = cap`. You need to prove the write-pointer stays in bounds.

```lean
buffer_bound (written remaining cap : Nat)
    (h1 : written + remaining = cap) (h2 : cap ≤ 1024) :
    written < 1025
```

From `h1` and `h2`: `written ≤ written + remaining = cap ≤ 1024 < 1025`.
`grind` chains these inequalities without guidance.
"

/-- A write-pointer stays within a bounded buffer. -/
TheoremDoc buffer_bound as "buffer_bound"

Statement buffer_bound (written remaining cap : Nat)
    (h1 : written + remaining = cap) (h2 : cap ≤ 1024) :
    written < 1025 := by
  Hint "`grind` has a built-in linear arithmetic solver. It combines `h1` and `h2`
  automatically to derive `written < 1025` — no hints needed."
  grind

Conclusion "
`grind`'s arithmetic engine derived `written ≤ cap ≤ 1024 < 1025` automatically.

When proofs mix equality reasoning (hypothesis substitution) with inequalities,
`grind` handles both simultaneously — unlike `omega`, which only does arithmetic,
or `simp`, which only rewrites.
"
