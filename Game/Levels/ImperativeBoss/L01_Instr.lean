import Game.Metadata
import Game.Levels.PurePrograms.L07_Expr

World "ImperativeBoss"
Level 1

Title "The Stack Machine"

Introduction "
Welcome to the **final boss world**!

Remember the `Expr` type and `eval` function from World 2?
```lean
inductive Expr where
  | num : Int → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr

def eval : Expr → Int
  | .num n     => n
  | .add e1 e2 => eval e1 + eval e2
  | .mul e1 e2 => eval e1 * eval e2
```

Now we are going to **compile** expressions to a stack machine and prove the compiler
correct. This is a classic program verification challenge — and it will exercise
everything you have learned across all 8 worlds.

A **stack machine** executes instructions one at a time, manipulating a stack of integers:
- `push n` pushes `n` onto the stack
- `add` pops two values, pushes their sum
- `mul` pops two values, pushes their product

```lean
inductive Instr where
  | push : Int → Instr
  | add  : Instr
  | mul  : Instr

def step : Instr → List Int → List Int
  | .push n, s           => n :: s
  | .add, x :: y :: rest  => (y + x) :: rest
  | .mul, x :: y :: rest  => (y * x) :: rest
  | _, s                  => s
```

The fallback `| _, s => s` handles stack underflow — it never occurs for compiled programs,
but makes `step` total (no `Option` needed).

**Your goal**: prove that `step (.push n) s = n :: s`. This is true by definition!
"

inductive Instr where
  | push : Int → Instr
  | add  : Instr
  | mul  : Instr
  deriving Repr, DecidableEq

def step : Instr → List Int → List Int
  | .push n, s           => n :: s
  | .add, x :: y :: rest  => (y + x) :: rest
  | .mul, x :: y :: rest  => (y * x) :: rest
  | _, s                  => s

@[simp] theorem step_push (n : Int) (s : List Int) : step (.push n) s = n :: s := by rfl
@[simp] theorem step_add (x y : Int) (rest : List Int) :
    step .add (x :: y :: rest) = (y + x) :: rest := by rfl
@[simp] theorem step_mul (x y : Int) (rest : List Int) :
    step .mul (x :: y :: rest) = (y * x) :: rest := by rfl

/-- `step (.push n) s = n :: s` -/
TheoremDoc step_push_stmt as "step_push_stmt"

Statement step_push_stmt : ∀ (n : Int) (s : List Int), step (.push n) s = n :: s := by
  Hint "This follows directly from the definition of `step`. Try `intro n s` then `rfl`."
  intro n s
  rfl

Conclusion "
`step (.push n)` simply prepends `n` to the stack — exactly what `rfl` confirms.

We now have the building blocks of a stack machine: `Instr` (the instruction set)
and `step` (single-instruction execution). Next, we will chain instructions together.
"

/-- Stack machine instructions: push, add, mul. -/
DefinitionDoc Instr as "Instr"
/-- Execute a single instruction on a stack. -/
DefinitionDoc step as "step"
NewDefinition Instr step
