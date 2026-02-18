import Game.Levels.PrePost.L03_Precondition
import Std.Tactic.Do
open Std Do

World "PrePost"
Level 4

Title "The Hoare Triple"

Introduction "
Time for the big idea: **Hoare triples**.

A Hoare triple has three parts:
```
⦃ precondition ⦄  program  ⦃ postcondition ⦄
```

It says: *if the precondition holds before the program runs, then the
postcondition holds after it finishes*.

In Lean's Std library, we write:
```lean
⦃⌜P⌝⦄ prog ⦃⇓ r => ⌜Q r⌝⦄
```

where `P` is the precondition, `prog` is an `Id` computation, `r` is the
return value, and `Q r` is the postcondition.

Here is a trivially simple program:
```lean
def pureSwap (a b : Nat) : Id (Nat × Nat) := do
  return (b, a)
```

The **`mvcgen`** tactic (*modular verification condition generator*) analyses
a `do` block and generates proof obligations automatically. Try it!
"

def pureSwap (a b : Nat) : Id (Nat × Nat) := do
  return (b, a)

/-- `pureSwap a b` returns `(b, a)`. -/
TheoremDoc pureSwap_correct as "pureSwap_correct"

Statement pureSwap_correct : ∀ (a b : Nat),
    ⦃⌜True⌝⦄ pureSwap a b ⦃⇓ r => ⌜r = (b, a)⌝⦄ := by
  Hint "First `intro a b` to name the inputs, then use `mvcgen [pureSwap]`
  to verify the triple automatically."
  intro a b
  mvcgen [pureSwap]

Conclusion "
`mvcgen [pureSwap]` unfolded the `do` block, checked that the return value
equals `(b, a)`, and closed the proof automatically.

This is the Hoare triple workflow:
1. **State the spec**: `⦃⌜P⌝⦄ prog ⦃⇓ r => ⌜Q r⌝⦄`
2. **Call `mvcgen`**: it generates verification conditions from the code.
3. **Close the VCs**: for simple programs, `mvcgen` does it all.

For programs with loops, you will need to supply a **loop invariant** — but
the workflow stays the same.
"

NewTactic mvcgen
/-- Swap two values (pure version). -/
DefinitionDoc pureSwap as "pureSwap"
NewDefinition pureSwap
