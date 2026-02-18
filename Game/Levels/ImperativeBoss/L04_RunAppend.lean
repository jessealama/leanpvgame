import Game.Levels.ImperativeBoss.L03_Compile

World "ImperativeBoss"
Level 4

Title "Composing Instruction Sequences"

Introduction "
The compiler concatenates instruction lists: `compile a ++ compile b ++ [.add]`.
To reason about this, we need a key lemma:

**Running concatenated instructions is the same as running them sequentially.**

```
run (is1 ++ is2) s = run is2 (run is1 s)
```

This is the structural heart of compiler correctness — it lets us break a compiled
program into pieces and reason about each piece independently.

The proof uses **`induction is1 generalizing s`**. Why `generalizing s`?
Because the inductive hypothesis must work for *any* stack, not just the original `s`.
When we step through `is1`, the stack changes at each step — so the IH needs to be
universally quantified over stacks.
"

/-- Running concatenated instructions equals running them sequentially. -/
TheoremDoc run_append as "run_append"

@[simp] Statement run_append : ∀ (is1 is2 : List Instr) (s : List Int),
    run (is1 ++ is2) s = run is2 (run is1 s) := by
  Hint "Start with `intro is1 is2 s`, then `induction is1 generalizing s`."
  intro is1 is2 s
  Hint "Now use `induction is1 generalizing s`. The `generalizing s` ensures the
  inductive hypothesis works for any stack, not just `s`."
  induction is1 generalizing s with
  | nil =>
    Hint "Base case: `is1 = []`. Try `simp [run]`."
    simp [run]
  | cons i is1 ih =>
    Hint "Inductive case: `is1 = i :: is1`. Try `simp [run, ih]`."
    simp [run, ih]

Conclusion "
`run_append` is the workhorse lemma for compiler correctness. It says:

> Running `is1 ++ is2` on stack `s` is the same as first running `is1` to get an
> intermediate stack, then running `is2` on that.

The key insight was `generalizing s` — without it, the IH would only apply to the
original stack, but we need it for `step i s` (the stack after one instruction).

With this lemma marked `@[simp]`, the compiler correctness proofs become almost automatic.
"

NewTheorem run_append
