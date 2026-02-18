import Game.Levels.FirstProofs.L03_ListLength

World "FirstProofs"
Level 4

Title "GCD Base Case"

Introduction "The **Euclidean algorithm** is one of the oldest algorithms in mathematics.
It computes the greatest common divisor (GCD) of two numbers:
```
def myGcd (a b : Nat) : Nat :=
  match b with
  | 0     => a
  | b' + 1 => myGcd (b' + 1) (a % (b' + 1))
```

The algorithm works by repeatedly replacing `(a, b)` with `(b, a % b)` until `b = 0`.

Prove the **base case**: when `b = 0`, `myGcd a 0 = a`."

def myGcd (a b : Nat) : Nat :=
  match b with
  | 0     => a
  | b' + 1 => myGcd (b' + 1) (a % (b' + 1))
termination_by b
decreasing_by
  exact Nat.mod_lt _ (Nat.succ_pos _)

/-- `myGcd a 0 = a` -/
TheoremDoc gcd_base as "gcd_base"

Statement gcd_base : ∀ (a : Nat), myGcd a 0 = a := by
  Hint "Try `intro a` then `simp [myGcd]`."
  intro a
  simp [myGcd]

Conclusion "`simp [myGcd]` matched the `| 0 => a` case of the definition and immediately
returned `a`. The base case is proved!

Notice `termination_by b`: this tells Lean that the second argument decreases at each
recursive call (since `a % (b' + 1) < b' + 1`). Without this, Lean would reject the definition."

NewTactic unfold
/-- Euclidean GCD algorithm. -/
DefinitionDoc myGcd as "myGcd"
NewDefinition myGcd
