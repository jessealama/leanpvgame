import Game.Levels.FirstProofs.L07_Primality
import Game.Levels.PurePrograms.L07_Expr

World "AutomationPower"
Level 1

Title "simp_all: Turbo-Charged Simplification"

Introduction "
**Welcome to World 3: Automation Power!**

You've proven programs correct one tactic at a time. In this world we hand
more work to Lean's automation — the same proofs that took five lines will
often collapse to one or two.

Our first new tool is **`simp_all`**. You already know `simp`, which simplifies
the *goal*. `simp_all` goes further: it simplifies both the *goal* **and every
hypothesis** in the context, then uses those simplified hypotheses to simplify
further — repeating until nothing changes.

The big win comes during **induction**: the induction hypothesis `ih` is
automatically incorporated. You never need to write `simp [ih]` again — just
`simp_all`.

**Compare the World 1 proof of this same theorem:**
```lean
-- World 1 (manual):
induction xs with
| nil          => simp
| cons x xs ih => simp [ih]; omega

-- World 3 (automated):
induction xs <;> simp_all <;> omega
```

Your goal is to prove that concatenating two lists produces a list whose
length is the sum of the parts. Use `induction xs` and let `simp_all`
handle the inductive step automatically.
"

/-- `(xs ++ ys).length = xs.length + ys.length` (proved with `simp_all`) -/
TheoremDoc append_length_auto as "append_length_auto"

Statement append_length_auto : ∀ (xs ys : List Nat),
    (xs ++ ys).length = xs.length + ys.length := by
  Hint "Try `induction xs <;> simp_all <;> omega`.
  The `<;>` combinator applies the next tactic to *all* remaining goals at once."
  intro xs ys
  induction xs <;> simp_all <;> omega

Conclusion "
`simp_all` found the induction hypothesis in the context and used it
automatically — no `[ih]` needed.

The `<;>` combinator is powerful: `induction xs <;> tac` applies `tac` to
**both** the base case and the inductive case. Combined with `simp_all`, a
5-line induction proof collapses to one line.
"

