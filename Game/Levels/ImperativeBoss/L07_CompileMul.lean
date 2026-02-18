import Game.Levels.ImperativeBoss.L06_CompileAdd

World "ImperativeBoss"
Level 7

Title "Compiler Correctness: Multiplication"

Introduction "
Same pattern as addition — now for multiplication.

```
compile (.mul a b) = compile a ++ compile b ++ [.mul]
```

The proof is structurally identical to the `add` case. See if you can do it
without the hint!
"

/-- Compiler correctness for multiplication. -/
TheoremDoc compile_mul as "compile_mul"

Statement compile_mul (a b : Expr) (s : List Int)
    (iha : ∀ s, run (compile a) s = eval a :: s)
    (ihb : ∀ s, run (compile b) s = eval b :: s) :
    run (compile (.mul a b)) s = eval (.mul a b) :: s := by
  Hint (hidden := true) "Same as addition: `simp [compile, eval, run_append, iha, ihb, run, step]`."
  simp [compile, eval, run_append, iha, ihb, run, step]

Conclusion "
Same technique, same result. The `add` and `mul` cases are symmetric —
the only difference is which arithmetic operation `step` performs.

You now have all three pieces of compiler correctness:
- **Base case**: numbers (L05)
- **Inductive case**: addition (L06)
- **Inductive case**: multiplication (L07)

Time to put them together into the full theorem!
"

NewTheorem compile_mul
