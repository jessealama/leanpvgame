import Game.Levels.ImperativeIntro.L02_Sum
import Std.Tactic.Do
open Std Do

World "ImperativeIntro"
Level 3

Title "Are All Elements Positive?"

Introduction "
Here is a loop that checks whether every element of an array is positive:

```lean
def allPositive (a : Array Nat) : Id Bool := do
  let mut ok := true
  for x in a do
    if x = 0 then ok := false
  return ok
```

The mutable flag `ok` starts as `true` and flips to `false` the moment we see a zero.

**Your goal**: prove that `allPositive a = true` exactly when every element is positive
(i.e. non-zero in `Nat`):
```
⦃⌜True⌝⦄ allPositive a ⦃⇓ r => ⌜r = true ↔ ∀ x ∈ a.toList, x ≠ 0⌝⦄
```

The invariant should relate `ok` to what has been seen so far:
```
mvcgen [allPositive] invariants
· ⇓⟨xs, ok⟩ => ⌜<your invariant>⌝
with grind
```
*Hint*: `ok = true ↔ ∀ x ∈ xs.prefix, x ≠ 0`.
"

def allPositive (a : Array Nat) : Id Bool := do
  let mut ok := true
  for x in a do
    if x = 0 then ok := false
  return ok

/-- `allPositive a = true` iff every element of `a` is non-zero. -/
TheoremDoc allPositive_correct as "allPositive_correct"

Statement allPositive_correct : ∀ (a : Array Nat),
    ⦃⌜True⌝⦄ allPositive a ⦃⇓ r => ⌜r = true ↔ ∀ x ∈ a.toList, x ≠ 0⌝⦄ := by
  Hint "Try `intro a`, then apply `mvcgen [allPositive]` with an invariant about `ok` and `xs.prefix`."
  intro a
  mvcgen [allPositive] invariants
  · ⇓⟨xs, ok⟩ => ⌜ok = true ↔ ∀ x ∈ xs.prefix, x ≠ 0⌝
  with grind

Conclusion "
The invariant `ok = true ↔ ∀ x ∈ xs.prefix, x ≠ 0` is the **specification itself**,
restricted to the prefix seen so far. This is the canonical shape for boolean-flag
invariants.

Notice the pattern: the flag `ok` summarises everything that has been checked.
Once the loop ends (`xs.suffix = []`), the invariant immediately gives us the full spec.
"

/-- Check whether all elements of an array are non-zero. -/
DefinitionDoc allPositive as "allPositive"
NewDefinition allPositive
