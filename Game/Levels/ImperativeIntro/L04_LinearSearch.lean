import Game.Levels.ImperativeIntro.L03_AllPositive
import Std.Tactic.Do
open Std Do

World "ImperativeIntro"
Level 4

Title "Linear Search"

Introduction "
What if we want to *find* an element and return early?

```lean
def findFirst (a : Array Nat) (target : Nat) : Id (Option Nat) := do
  let mut result : Option Nat := none
  for x in a do
    if result.isNone && x = target then
      result := some x
  return result
```

This records the first match it finds (or `none` if there is no match).

**Your goal**: prove that `findFirst a target` returns `some target` when `target` is in
the array, and `none` otherwise:
```
⦃⌜True⌝⦄ findFirst a target ⦃⇓ r => ⌜r = none ↔ target ∉ a.toList⌝⦄
```

The invariant should relate `result` to the prefix seen so far:
*Hint*: `result = none ↔ target ∉ xs.prefix`.
"

def findFirst (a : Array Nat) (target : Nat) : Id (Option Nat) := do
  let mut result : Option Nat := none
  for x in a do
    if result.isNone && x = target then
      result := some x
  return result

/-- `findFirst a target = none` iff `target ∉ a.toList`. -/
TheoremDoc findFirst_correct as "findFirst_correct"

Statement findFirst_correct : ∀ (a : Array Nat) (target : Nat),
    ⦃⌜True⌝⦄ findFirst a target ⦃⇓ r => ⌜r = none ↔ target ∉ a.toList⌝⦄ := by
  Hint "Try `intro a target`, then `mvcgen [findFirst]` with an invariant about `result` and `xs.prefix`."
  intro a target
  mvcgen [findFirst] invariants
  · ⇓⟨xs, result⟩ => ⌜result = none ↔ target ∉ xs.prefix⌝
  with grind

Conclusion "
The invariant `result = none ↔ target ∉ xs.prefix` is again the specification restricted
to the prefix. Once the loop finishes, `xs.prefix = a.toList` and the invariant gives us
exactly what we want.

Note that we used a simple accumulator rather than an early `return` — `mvcgen` supports
early return too, but the accumulator version keeps the invariant straightforward.
"

/-- Find the first occurrence of `target` in `a`, returning `none` if absent. -/
DefinitionDoc findFirst as "findFirst"
NewDefinition findFirst
