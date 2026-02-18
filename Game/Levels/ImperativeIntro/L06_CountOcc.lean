import Game.Levels.ImperativeIntro.L05_FindMax
import Std.Tactic.Do
open Std Do

World "ImperativeIntro"
Level 6

Title "Count Occurrences"

Introduction "
The final level: count how many times a value appears in an array.

```lean
def countOcc (a : Array Nat) (v : Nat) : Id Nat := do
  let mut cnt := 0
  for x in a do
    if x = v then cnt := cnt + 1
  return cnt
```

**Your goal**: prove that `countOcc a v` equals the number of times `v` appears:
```
⦃⌜True⌝⦄ countOcc a v ⦃⇓ r => ⌜r = (a.toList.filter (· = v)).length⌝⦄
```

The invariant is literally the spec restricted to the prefix:
*Hint*: `cnt = (xs.prefix.filter (· = v)).length`.
"

def countOcc (a : Array Nat) (v : Nat) : Id Nat := do
  let mut cnt := 0
  for x in a do
    if x = v then cnt := cnt + 1
  return cnt

/-- `countOcc a v = (a.toList.filter (· = v)).length` -/
TheoremDoc countOcc_correct as "countOcc_correct"

Statement countOcc_correct : ∀ (a : Array Nat) (v : Nat),
    ⦃⌜True⌝⦄ countOcc a v ⦃⇓ r => ⌜r = (a.toList.filter (· = v)).length⌝⦄ := by
  Hint "Try `intro a v`, then `mvcgen [countOcc]` with a counting-prefix invariant."
  intro a v
  mvcgen [countOcc] invariants
  · ⇓⟨xs, cnt⟩ => ⌜cnt = (xs.prefix.filter (· = v)).length⌝
  with grind

Conclusion "
The invariant is the specification itself, restricted to `xs.prefix`.
This is the hallmark of a clean imperative proof: the invariant is so natural
that it almost writes itself.

You have now verified 6 imperative programs — from a simple swap to a counting loop —
all using the same `mvcgen → invariant → grind` workflow.

**Congratulations — you've completed the Imperative Intro world!**

The reversal algorithm and more advanced patterns await in the next world.
"

/-- Count the number of times `v` appears in array `a`. -/
DefinitionDoc countOcc as "countOcc"
NewDefinition countOcc
