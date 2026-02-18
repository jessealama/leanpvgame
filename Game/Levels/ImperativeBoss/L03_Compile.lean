import Game.Levels.ImperativeBoss.L02_Run

World "ImperativeBoss"
Level 3

Title "The Compiler"

Introduction "
Now for the star of the show: a compiler from `Expr` to stack machine instructions.

The idea is **postfix** (reverse Polish) compilation:
- A number `n` compiles to `[.push n]`
- `add a b` compiles to `compile a ++ compile b ++ [.add]`
- `mul a b` compiles to `compile a ++ compile b ++ [.mul]`

```lean
def compile : Expr → List Instr
  | .num n   => [.push n]
  | .add a b => compile a ++ compile b ++ [.add]
  | .mul a b => compile a ++ compile b ++ [.mul]
```

For example, `3 * (1 + 2)` compiles to `[.push 3, .push 1, .push 2, .add, .mul]`.

**Your goal**: verify that compiling and running `3 * (1 + 2)` yields `[9]`.
"

def compile : Expr → List Instr
  | .num n   => [.push n]
  | .add a b => compile a ++ compile b ++ [.add]
  | .mul a b => compile a ++ compile b ++ [.mul]

/-- `run (compile (3 * (1 + 2))) [] = [9]` -/
TheoremDoc compile_example as "compile_example"

Statement compile_example :
    run (compile (.mul (.num 3) (.add (.num 1) (.num 2)))) [] = [9] := by
  Hint "Another concrete computation — `native_decide` handles it."
  native_decide

Conclusion "
The compiler produced `[.push 3, .push 1, .push 2, .add, .mul]`, and the stack machine
executed it to get `[9]` — matching `eval (.mul (.num 3) (.add (.num 1) (.num 2))) = 9`.

But can we prove this works for **all** expressions, not just this example? That is the
compiler correctness theorem, and the next few levels build up to it piece by piece.
"

/-- Compile an expression to stack machine instructions (postfix). -/
DefinitionDoc compile as "compile"
NewDefinition compile
