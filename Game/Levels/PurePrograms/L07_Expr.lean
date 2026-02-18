import Game.Levels.PurePrograms.L06_BST

World "PurePrograms"
Level 7

Title "Expression Evaluator"

Introduction "
Let's build a tiny **expression language** — the kind at the heart of every compiler
and interpreter.

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

`eval` is structurally recursive on `Expr`, so Lean accepts it automatically.

**Your goal**: prove the distributive law — `a * (b + c) = a*b + a*c` — at the
expression level.

After `simp [eval]` unfolds the evaluator, the goal becomes a pure arithmetic
identity on `Int`. Lean knows this as `Int.mul_add`, so
`simp [eval, Int.mul_add]` closes it in one step.
"

inductive Expr where
  | num : Int → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr

def eval : Expr → Int
  | .num n     => n
  | .add e1 e2 => eval e1 + eval e2
  | .mul e1 e2 => eval e1 * eval e2

/-- `eval (Mul e (Add e1 e2)) = eval (Add (Mul e e1) (Mul e e2))` -/
TheoremDoc eval_distributes as "eval_distributes"

Statement eval_distributes : ∀ (a b c : Expr),
    eval (.mul a (.add b c)) = eval (.mul a b) + eval (.mul a c) := by
  intro a b c
  simp [eval, Int.mul_add]

Conclusion "
World 2 complete! You've built and verified:
- **`myMap`**, **`myFilter`**, **`myFoldr`** — the classic list combinators
- **`half`** — a non-structural recursion with explicit termination proof
- **`Tree`** and **`treeHeight`** — your own inductive type
- **`bstInsert`/`bstMember`** — BST insert-then-search correctness
- **`Expr`/`eval`** — a verified expression evaluator

Onward to World 3: Subtypes!
"

/-- Abstract syntax tree for arithmetic expressions. -/
DefinitionDoc Expr as "Expr"
/-- Evaluate an expression to an integer. -/
DefinitionDoc eval as "eval"
NewDefinition Expr eval
/-- `a * (b + c) = a * b + a * c` -/
TheoremDoc Int.mul_add as "Int.mul_add"
NewTheorem Int.mul_add
