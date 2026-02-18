import Game.Levels.ImperativeBoss.L09_Exec

World "ImperativeBoss"
Level 10

Title "A Verified Compiler"

Introduction "
The headline theorem — the one sentence that says it all:

```
∀ (e : Expr), run (compile e) [] = [eval e]
```

Running the compiled instructions on an empty stack produces a stack containing
exactly the evaluated result. Nothing more, nothing less.

This follows directly from `compile_correct` (L08) — just plug in `s = []`.
"

/-- The headline theorem: compiling and running produces eval. -/
TheoremDoc verified_compiler as "verified_compiler"

Statement verified_compiler : ∀ (e : Expr), run (compile e) [] = [eval e] := by
  Hint "This is a direct consequence of `compile_correct`. Try `intro e` then
  `exact compile_correct e []`."
  intro e
  exact compile_correct e []

Conclusion "
**Congratulations — you have built a verified compiler!**

Let's look back at what you accomplished:

**The compilation pipeline:**
```
Expr  ──compile──▶  List Instr  ──run/exec──▶  result = eval e
```

**The theorems:**
- `compile_correct` (L08): `run (compile e) s = eval e :: s`
- `exec_correct` (L09): the imperative executor matches `foldl step`
- `run_eq_foldl` (L09): bridges recursive `run` and iterative `foldl`
- `verified_compiler` (L10): `run (compile e) [] = [eval e]`

**The techniques you used:**
- Structural induction with `generalizing` (L04, L08)
- Building up `@[simp]` lemmas for compositional reasoning (L01, L04)
- Hoare triples and `mvcgen` for imperative verification (L09)
- Connecting functional and imperative implementations (L09)

You started this game proving `double n = n + n`, and now you have verified
an end-to-end compilation pipeline. That is the power of formal verification:
**mathematical certainty that your software is correct**.

Thank you for playing the Program Verification Game!
"

NewTheorem verified_compiler
