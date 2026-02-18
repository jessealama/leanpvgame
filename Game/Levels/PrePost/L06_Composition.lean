import Game.Levels.PrePost.L05_MutableSwap

World "PrePost"
Level 6

Title "Contract Composition"

Introduction "
The real power of contracts: they **compose**.

If function `f` has a contract `P → Q` and function `g` has a contract `Q → R`,
then the pipeline `g ∘ f` has contract `P → R`. The postcondition of `f` becomes
the precondition of `g`.

No need for Hoare triples here — this is a pure logical principle.
You have all the hypotheses you need; chain them together.
"

/-- Contracts compose: post of f feeds into pre of g. -/
TheoremDoc spec_compose as "spec_compose"

Statement spec_compose
    (f : Nat → Nat) (g : Nat → Nat)
    (P : Nat → Prop) (Q : Nat → Prop) (R : Nat → Prop)
    (hf : ∀ x, P x → Q (f x))
    (hg : ∀ y, Q y → R (g y)) :
    ∀ x, P x → R (g (f x)) := by
  Hint "Introduce `x` and `hx : P x`, then chain the hypotheses:
  `hf x hx` gives `Q (f x)`, and `hg (f x) ...` gives `R (g (f x))`.

  Try `intro x hx` then `exact hg (f x) (hf x hx)`."
  intro x hx
  exact hg (f x) (hf x hx)

Conclusion "
Congratulations — you have completed **Pre/Post Conditions**!

What you learned:
- **Postconditions**: what a function guarantees (Levels 1–2)
- **Preconditions**: what a function requires (Level 3)
- **Hoare triples**: `⦃⌜P⌝⦄ prog ⦃⇓ r => ⌜Q r⌝⦄` (Level 4)
- **Mutable state**: same verification workflow (Level 5)
- **Composition**: postcondition of one = precondition of next (Level 6)

This is the foundation of **formal program verification**. In the next world,
you will verify imperative programs with loops — using loop invariants and
the same `mvcgen` workflow.

Onward to **Imperative Intro**!
"
