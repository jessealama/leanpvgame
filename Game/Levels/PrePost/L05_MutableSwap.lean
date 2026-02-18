import Game.Levels.PrePost.L04_HoareTriple
import Std.Tactic.Do
open Std Do

World "PrePost"
Level 5

Title "Mutable State"

Introduction "
Here is the same swap, but written with `let mut` — mutable local variables:

```lean
def mutableSwap (a b : Nat) : Id (Nat × Nat) := do
  let mut x := a
  let mut y := b
  let t := x
  x := y
  y := t
  return (x, y)
```

`Id` is Lean's *identity monad* — it runs imperatively but has no side effects
beyond tracking mutable locals.

Does mutation make the proof harder? Try it and find out!
"

def mutableSwap (a b : Nat) : Id (Nat × Nat) := do
  let mut x := a
  let mut y := b
  let t := x
  x := y
  y := t
  return (x, y)

/-- `mutableSwap a b` returns `(b, a)`. -/
TheoremDoc mutableSwap_correct as "mutableSwap_correct"

Statement mutableSwap_correct : ∀ (a b : Nat),
    ⦃⌜True⌝⦄ mutableSwap a b ⦃⇓ r => ⌜r = (b, a)⌝⦄ := by
  Hint "Same pattern as before: `intro a b` then `mvcgen [mutableSwap]`."
  intro a b
  mvcgen [mutableSwap]

Conclusion "
The exact same proof! `mvcgen` tracks the mutable assignments step by step:
- After `let mut x := a; let mut y := b`: x = a, y = b
- After `let t := x; x := y; y := t`: x = b, y = a
- At `return (x, y)`: the result is `(b, a)`

Mutable local variables are just syntactic sugar in Lean — `mvcgen` handles
them the same way as pure `let` bindings. The verification is identical.
"

/-- Swap two values using mutable locals. -/
DefinitionDoc mutableSwap as "mutableSwap"
NewDefinition mutableSwap
