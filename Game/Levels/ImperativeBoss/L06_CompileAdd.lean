import Game.Levels.ImperativeBoss.L05_CompileNum

World "ImperativeBoss"
Level 6

Title "Compiler Correctness: Addition"

Introduction "
Now for the `add` case. The compiler produces:
```
compile (.add a b) = compile a ++ compile b ++ [.add]
```

Running this on stack `s`:
1. `run (compile a) s` gives `eval a :: s` (by IH for `a`)
2. `run (compile b) (eval a :: s)` gives `eval b :: eval a :: s` (by IH for `b`)
3. `run [.add] (eval b :: eval a :: s)` gives `(eval a + eval b) :: s`

And `eval (.add a b) = eval a + eval b`, so `run (compile (.add a b)) s = eval (.add a b) :: s`.

The `run_append` lemma does the heavy lifting: it splits the concatenated instruction
list into sequential runs. Then `simp` with the inductive hypotheses closes the goal.

In this level, the inductive hypotheses are given to you as explicit assumptions
`iha` and `ihb`. In L08, you will use `induction ... generalizing` to generate them
yourself.
"

/-- Compiler correctness for addition. -/
TheoremDoc compile_add as "compile_add"

Statement compile_add (a b : Expr) (s : List Int)
    (iha : ∀ s, run (compile a) s = eval a :: s)
    (ihb : ∀ s, run (compile b) s = eval b :: s) :
    run (compile (.add a b)) s = eval (.add a b) :: s := by
  Hint "Try `simp [compile, eval, run_append, iha, ihb, run, step]`.
  `run_append` splits the concatenation, `iha`/`ihb` handle the subexpressions,
  and `run`/`step` finish the last instruction."
  simp [compile, eval, run_append, iha, ihb, run, step]

Conclusion "
One `simp` call closed the entire goal! Here is what happened:
- `compile` unfolded `.add a b` to `compile a ++ compile b ++ [.add]`
- `run_append` split this into three sequential runs
- `iha` and `ihb` simplified the first two runs
- `run` and `step` handled the final `[.add]` instruction
- `eval` matched the result

This is the power of building up the right lemmas (`run_append`, `step_*`).
"

NewTheorem compile_add
