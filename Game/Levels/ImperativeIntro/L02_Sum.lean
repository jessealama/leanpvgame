import Game.Levels.ImperativeIntro.L01_Swap
import Std.Tactic.Do
open Std Do

World "ImperativeIntro"
Level 2

Title "Summing an Array"

Introduction "
Time to add a loop! Here is a classic accumulator:

```lean
def sumArray (a : Array Nat) : Id Nat := do
  let mut s := 0
  for x in a do
    s := s + x
  return s
```

For loop proofs, `mvcgen` needs a **loop invariant** — a property that holds at the
start of every loop iteration. You supply it with the `invariants` keyword:

```
mvcgen [sumArray] invariants
· <your invariant here>
with grind
```

The invariant here should relate the running sum `s` to the elements of `a` seen so far.
Think: *what does `s` equal after processing the first `i` elements?*

The loop variable is a `List.Cursor` named `xs` (tracking which elements have been seen),
and `s` is the running sum. Use:
```
mvcgen [sumArray] invariants
· ⇓⟨xs, s⟩ => ⌜<your invariant about xs and s>⌝
with grind
```
*Hint*: `xs.prefix` is the list of elements processed so far.
`xs.prefix.foldl (· + ·) 0` is their sum.
"

def sumArray (a : Array Nat) : Id Nat := do
  let mut s := 0
  for x in a do
    s := s + x
  return s

/-- `sumArray a = a.foldl (· + ·) 0` -/
TheoremDoc sum_correct as "sum_correct"

Statement sum_correct : ∀ (a : Array Nat),
    ⦃⌜True⌝⦄ sumArray a ⦃⇓ r => ⌜r = a.foldl (· + ·) 0⌝⦄ := by
  Hint "Try `intro a`, then `mvcgen [sumArray] invariants? with grind` to see
  what invariant skeleton `mvcgen` suggests."
  intro a
  mvcgen [sumArray] invariants
  · ⇓⟨xs, s⟩ => ⌜s = xs.prefix.foldl (· + ·) 0⌝
  with grind

Conclusion "
The invariant `s = xs.prefix.foldl (· + ·) 0` captures exactly what the
accumulator `s` equals after the loop has processed `xs.prefix`.

`mvcgen` checked three things for you:
- **Initialisation**: `s = 0 = foldl of []` before the loop starts.
- **Preservation**: if the invariant holds before an iteration, it holds after.
- **Postcondition**: when the loop ends (`xs.suffix = []`), the invariant implies the spec.

`grind` proved all three automatically once you stated the right invariant.

*Tip*: If you are unsure what invariant to write, use `mvcgen [sumArray] invariants?`
and Lean will suggest a skeleton!
"


/-- Sum all elements of an array. -/
DefinitionDoc sumArray as "sumArray"
NewDefinition sumArray
