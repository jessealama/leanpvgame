import Game.Levels.ImperativeBoss.L07_CompileMul

World "ImperativeBoss"
Level 8

Title "The Correctness Theorem"

Introduction "
This is it — the **compiler correctness theorem**:

```
∀ (e : Expr) (s : List Int), run (compile e) s = eval e :: s
```

For *any* expression `e` and *any* initial stack `s`, running the compiled instructions
produces a stack with `eval e` on top and `s` unchanged below.

You proved each case separately in L05–L07. Now combine them using
**`induction e generalizing s`**.

Why `generalizing s`? The inductive hypotheses for `add` and `mul` need to work
for *any* stack — not just the original `s`. When you process `compile a ++ compile b ++ [.add]`,
the stack changes between each piece: `s → eval a :: s → eval b :: eval a :: s → ...`.
The IH must apply at each intermediate stack.
"

/-- Compiler correctness: running compiled code produces eval on the stack. -/
TheoremDoc compile_correct as "compile_correct"

Statement compile_correct : ∀ (e : Expr) (s : List Int),
    run (compile e) s = eval e :: s := by
  Hint "Start with `intro e s` then `induction e generalizing s`.
  Each case matches a level you already proved (L05, L06, L07)."
  intro e s
  induction e generalizing s with
  | num n =>
    Hint "Base case: `e = .num n`. Same proof as L05."
    simp [compile, run, step, eval]
  | add a b iha ihb =>
    Hint "Inductive case: `e = .add a b`. Same proof as L06, but `iha`/`ihb` come
    from the induction principle instead of being given as assumptions."
    simp [compile, eval, run_append, iha, ihb, run, step]
  | mul a b iha ihb =>
    Hint "Inductive case: `e = .mul a b`. Same proof as L07."
    simp [compile, eval, run_append, iha, ihb, run, step]

Conclusion "
**The compiler is correct!**

For any expression `e`, the compiled instruction sequence, when run on any stack `s`,
produces `eval e :: s`. The key ingredients:
- `run_append` (L04) — splits concatenated programs
- `induction e generalizing s` — gives universally quantified IH
- `simp` with the right lemmas — closes each case

This is a theorem about *all* expressions — infinitely many programs, all verified
with one proof.
"

NewTheorem compile_correct
