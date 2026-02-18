import Game.Levels.Termination.L05_MergeLength

World "Termination"
Level 6

Title "Chaining Total Functions"

Introduction "
You have now proved:
- `myGcd_self` (Level 1): `myGcd n n = n`
- `myLog2_pos` (Level 3): `2 ≤ n → 0 < myLog2 n`

Both functions are **total** — Lean verified their termination. That means you
can freely compose and chain results about them.

Prove: for any `n ≥ 2`, taking the GCD of `n` with itself and then computing
its log gives a positive result.

This should take exactly two steps.
"

/-- Composition of `myGcd_self` and `myLog2_pos`: a chain of total functions. -/
TheoremDoc termination_victory as "termination_victory"

Statement termination_victory (n : Nat) (h : 2 ≤ n) :
    0 < myLog2 (myGcd n n) := by
  Hint "Use `rw [myGcd_self]` to simplify `myGcd n n` to `n`."
  rw [myGcd_self]
  Hint "Now apply `myLog2_pos n h` to close the goal."
  exact myLog2_pos n h

Conclusion "
Congratulations — you have completed **World 5: Termination**!

You have proved that four recursive functions terminate and reasoned about their
behavior:
- `myGcd`: the Euclidean algorithm (measure: second argument)
- `myDiv`: division by subtraction (measure: dividend)
- `myLog2`: logarithm by halving (measure: value)
- `merge`: sorted merge (measure: combined list length)

The key insight: once Lean has verified a termination proof, every theorem you
prove about the function holds for *all* inputs — no special cases, no partiality.

**World 6** awaits: Data Invariants. You will prove that data structures like
sorted lists and balanced trees maintain their invariants through every operation.
"

NewTheorem termination_victory
