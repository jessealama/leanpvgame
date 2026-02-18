import Game.Levels.ImperativeBoss.L08_CompileCorrect
import Std.Tactic.Do
open Std Do

World "ImperativeBoss"
Level 9

Title "The Imperative Executor"

Introduction "
We proved that `run` (a pure recursive function) correctly executes compiled code.
But real machines use loops, not recursion. Let's write an **imperative executor**:

```lean
def exec (instrs : Array Instr) : Id (List Int) := do
  let mut stack : List Int := []
  for i in instrs do
    stack := step i stack
  return stack
```

This is exactly the kind of loop you verified in the Imperative Intro world!
The invariant follows the familiar pattern: relate the mutable variable to the
prefix of elements processed so far.

We also need a bridge lemma connecting `run` (recursive) to `foldl` (what the loop computes):
```lean
theorem run_eq_foldl (instrs : List Instr) (s : List Int) :
    run instrs s = instrs.foldl (fun s i => step i s) s
```

**Your goal**: verify the imperative executor using `mvcgen`.
"

theorem run_eq_foldl (instrs : List Instr) (s : List Int) :
    run instrs s = instrs.foldl (fun s i => step i s) s := by
  induction instrs generalizing s with
  | nil => simp [run]
  | cons i rest ih => simp [run, ih]

def exec (instrs : Array Instr) : Id (List Int) := do
  let mut stack : List Int := []
  for i in instrs do
    stack := step i stack
  return stack

/-- `exec instrs` computes the same result as folding `step` over the instructions. -/
TheoremDoc exec_correct as "exec_correct"

Statement exec_correct : ∀ (instrs : Array Instr),
    ⦃⌜True⌝⦄ exec instrs ⦃⇓ r => ⌜r = instrs.toList.foldl (fun s i => step i s) []⌝⦄ := by
  Hint "Try `intro instrs` then use `mvcgen [exec] invariants` with a foldl-over-prefix
  invariant, just like `sumArray` and `countOcc` from the Imperative Intro world."
  intro instrs
  mvcgen [exec] invariants
  · ⇓⟨xs, stack⟩ => ⌜stack = xs.prefix.foldl (fun s i => step i s) []⌝
  with grind

Conclusion "
The imperative executor is verified! The invariant says:

> After processing `xs.prefix` (the instructions seen so far), `stack` equals
> `foldl step` over that prefix.

This is exactly the same pattern as `sumArray`: the invariant is the spec restricted
to the prefix.

The `run_eq_foldl` lemma bridges the two worlds:
- `run` (recursive, used in `compile_correct`)
- `foldl` (what the `for` loop computes)

One more level to bring it all together!
"

/-- Imperative stack machine executor using a for loop. -/
DefinitionDoc exec as "exec"
/-- `run instrs s = instrs.foldl (fun s i => step i s) s` -/
TheoremDoc run_eq_foldl as "run_eq_foldl"
NewDefinition exec
NewTheorem exec_correct run_eq_foldl
