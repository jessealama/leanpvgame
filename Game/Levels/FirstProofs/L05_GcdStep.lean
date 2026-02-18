import Game.Levels.FirstProofs.L04_GcdBase

World "FirstProofs"
Level 5

Title "GCD Step"

Introduction "Now prove the **recursive step** of the Euclidean algorithm:
when `b ≠ 0`, `myGcd a b` reduces to `myGcd b (a % b)`.

```
b ≠ 0 → myGcd a b = myGcd b (a % b)
```

*Tip*: Use `cases b` to split into `b = 0` (contradiction) and `b = b' + 1`
(where `simp [myGcd]` applies the second equation of the definition)."

/-- When `b ≠ 0`, `myGcd a b = myGcd b (a % b)`. -/
TheoremDoc gcd_step as "gcd_step"

Statement gcd_step : ∀ (a b : Nat), b ≠ 0 → myGcd a b = myGcd b (a % b) := by
  Hint "Use `intro a b h`, then `cases b` to split on whether `b = 0` or `b = b' + 1`."
  intro a b h
  cases b with
  | zero =>
    Hint "In this case `b = 0` but `h : 0 ≠ 0`. This is a contradiction — try `omega`."
    omega
  | succ b' =>
    Hint "Now `b = b' + 1`. Try `simp [myGcd]` to apply the recursive equation."
    simp [myGcd]

Conclusion "`cases b` split the proof into two cases:
- `b = 0`: contradicts `h : 0 ≠ 0`, closed by `omega`.
- `b = b' + 1`: `simp [myGcd]` applied the second equation of the definition,
  giving `myGcd (b'+1) (a % (b'+1)) = myGcd (b'+1) (a % (b'+1))`.

Together with `gcd_base`, you have now verified **both equations** of the
Euclidean algorithm!

*Coming up*: when both cases of a `cases` (or `induction`) need the **same** tactic,
you can write `cases b <;> tac` to apply `tac` to every goal at once — no need to
list each case separately. You'll see this in the next level."

NewTactic cases
