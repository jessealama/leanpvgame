import Game.Levels.ImperativeIntro.L04_LinearSearch
import Std.Tactic.Do
open Std Do

World "ImperativeIntro"
Level 5

Title "Running Maximum"

Introduction "
A classic pattern: maintain the largest element seen so far.

```lean
def findMax (a : Array Nat) (default : Nat) : Id Nat := do
  let mut curMax := default
  for x in a do
    if x > curMax then curMax := x
  return curMax
```

`curMax` starts at `default` and is updated whenever we see a larger element.

**Your goal**: prove that `findMax` computes the same result as `List.foldl max default`:
```
⦃⌜True⌝⦄ findMax a d ⦃⇓ r => ⌜r = a.toList.foldl max d⌝⦄
```

The invariant should relate `curMax` to the maximum of the prefix:
*Hint*: `curMax = xs.prefix.foldl max d`.
"

def findMax (a : Array Nat) (default : Nat) : Id Nat := do
  let mut curMax := default
  for x in a do
    if x > curMax then curMax := x
  return curMax

/-- `findMax a d = a.toList.foldl max d` -/
TheoremDoc findMax_correct as "findMax_correct"

Statement findMax_correct : ∀ (a : Array Nat) (d : Nat),
    ⦃⌜True⌝⦄ findMax a d ⦃⇓ r => ⌜r = a.toList.foldl max d⌝⦄ := by
  Hint "Try `intro a d`, then `mvcgen [findMax]` with the running-max invariant."
  intro a d
  mvcgen [findMax] invariants
  · ⇓⟨xs, curMax⟩ => ⌜curMax = xs.prefix.foldl max d⌝
  with grind

Conclusion "
The invariant `curMax = xs.prefix.foldl max d` mirrors exactly how `curMax` is built:
taking the maximum of the default and all elements seen so far.

This *running-aggregate* pattern appears in many algorithms:
- Replace `max` with `+` → you get the sum invariant from Level 2.
- Replace `max` with `&&` → you get a boolean-flag invariant like Level 3.

The invariant is always the spec restricted to the prefix seen so far.
"

/-- Find the maximum element of an array, returning `default` for the empty array. -/
DefinitionDoc findMax as "findMax"
NewDefinition findMax
