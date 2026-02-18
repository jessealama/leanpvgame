import Game.Levels.ImperativeBoss.L04_RunAppend

World "ImperativeBoss"
Level 5

Title "Compiler Correctness: Numbers"

Introduction "
Now we begin proving compiler correctness — the theorem that running compiled code
produces the same result as evaluating the expression.

The full theorem is:
```
∀ (e : Expr) (s : List Int), run (compile e) s = eval e :: s
```

We will prove it case by case, starting with the base case: **number literals**.

Compiling `.num n` produces `[.push n]`. Running that on any stack `s` gives `n :: s`.
And `eval (.num n) = n`. So `run (compile (.num n)) s = eval (.num n) :: s`.

This follows directly from the definitions.
"

/-- Compiler correctness for number literals. -/
TheoremDoc compile_num as "compile_num"

Statement compile_num : ∀ (n : Int) (s : List Int),
    run (compile (.num n)) s = eval (.num n) :: s := by
  Hint "Unfold the definitions with `simp [compile, run, step, eval]`."
  intro n s
  simp [compile, run, step, eval]

Conclusion "
The base case is straightforward: `compile (.num n) = [.push n]`, and
`run [.push n] s = n :: s = eval (.num n) :: s`.

Next: the inductive cases for `add` and `mul`.
"

NewTheorem compile_num
