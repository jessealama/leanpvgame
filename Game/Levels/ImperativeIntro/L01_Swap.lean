import Game.Metadata
import Std.Tactic.Do
open Std Do

World "ImperativeIntro"
Level 1

Title "Your First Imperative Proof"

Introduction "
Welcome to **Imperative Verification**!

So far you have proved properties of *pure* functions — functions with no mutable state.
Now we will verify programs that look imperative: they use `let mut` variables and
reassign them inside `do` blocks.

Here is a tiny example: swapping two values.

```lean
def swap (a b : Nat) : Id (Nat × Nat) := do
  let mut x := a
  let mut y := b
  let t := x
  x := y
  y := t
  return (x, y)
```

`Id` is Lean's *identity monad* — it runs imperatively but has no side effects beyond
tracking mutable locals. `Id.run` extracts the value.

**Hoare triples** let us specify what a program guarantees:
```
⦃ precondition ⦄  program  ⦃ postcondition ⦄
```
For `swap`: `⦃⌜True⌝⦄ swap a b ⦃⇓ r => ⌜r = (b, a)⌝⦄` says: starting from *any* state,
`swap a b` returns the pair `(b, a)`.

The new tactic **`mvcgen [swap]`** breaks this triple into simple proof obligations
(*verification conditions*) automatically — you just need to close them.
"

def swap (a b : Nat) : Id (Nat × Nat) := do
  let mut x := a
  let mut y := b
  let t := x
  x := y
  y := t
  return (x, y)

/-- `swap a b` returns `(b, a)`. -/
TheoremDoc swap_correct as "swap_correct"

Statement swap_correct : ∀ (a b : Nat), ⦃⌜True⌝⦄ swap a b ⦃⇓ r => ⌜r = (b, a)⌝⦄ := by
  Hint "Try `intro a b` then `mvcgen [swap]`."
  intro a b
  mvcgen [swap]

Conclusion "
`mvcgen [swap]` analysed the `do` block and discharged all verification conditions
automatically! Since `swap` has no loops, there were no invariants needed — `mvcgen`
unfolded the sequential assignments and closed the resulting equalities on its own.

For programs with loops we will need to supply a **loop invariant**, but the rest of
the workflow stays the same:
1. State the spec as `⦃⌜P⌝⦄ prog ⦃⇓ r => ⌜Q r⌝⦄`.
2. Call `mvcgen [prog]` to generate the VCs.
3. Supply invariants and close VCs with `grind`.
"


/-- Swap two values: `swap a b = (b, a)`. -/
DefinitionDoc swap as "swap"
NewDefinition swap
