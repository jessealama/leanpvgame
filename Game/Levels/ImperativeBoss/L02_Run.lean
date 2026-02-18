import Game.Levels.ImperativeBoss.L01_Instr

World "ImperativeBoss"
Level 2

Title "Running Instructions"

Introduction "
A single `step` executes one instruction. To run an entire program, we apply
instructions one after another:

```lean
def run : List Instr → List Int → List Int
  | [], stack       => stack
  | i :: rest, stack => run rest (step i stack)
```

`run` is structurally recursive on the instruction list, so Lean accepts it
automatically.

**Your goal**: compute `run [.push 2, .push 3, .add] []` and verify it equals `[5]`.

Since this is a concrete computation, `native_decide` can evaluate it directly.
"

def run : List Instr → List Int → List Int
  | [], stack       => stack
  | i :: rest, stack => run rest (step i stack)

@[simp] theorem run_nil (s : List Int) : run [] s = s := by rfl
@[simp] theorem run_cons (i : Instr) (rest : List Instr) (s : List Int) :
    run (i :: rest) s = run rest (step i s) := by rfl

/-- `run [.push 2, .push 3, .add] [] = [5]` -/
TheoremDoc run_example as "run_example"

Statement run_example : run [.push 2, .push 3, .add] [] = [5] := by
  Hint "This is a concrete computation. Try `native_decide`."
  native_decide

Conclusion "
`native_decide` evaluated the entire execution trace:
1. `run [.push 2, .push 3, .add] []`
2. `→ run [.push 3, .add] [2]`
3. `→ run [.add] [3, 2]`
4. `→ run [] [5]`
5. `→ [5]`

With `run` in hand, we can execute any sequence of stack machine instructions.
Next: we will write a **compiler** that translates `Expr` into `List Instr`.
"

/-- Execute a list of instructions on a stack. -/
DefinitionDoc run as "run"
NewDefinition run
