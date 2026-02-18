import Game.Levels.AutomationPower.L07_FilterMap

World "Termination"
Level 1

Title "A Familiar Function, New Property"

Introduction "
You already proved things *about* `myGcd` in World 1 — the base case and the
step lemma. Here is the definition again, with its termination proof:

```lean
def myGcd (a b : Nat) : Nat :=
  match b with
  | 0     => a
  | b' + 1 => myGcd (b' + 1) (a % (b' + 1))
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)
```

`termination_by b` says: the second argument strictly decreases at every
recursive call. `a % (b'+1) < b'+1`, so the algorithm always reaches `b = 0`.

Because Lean has *checked* this termination proof, you can reason about `myGcd`
for **any** input — including `myGcd n n`, which was not covered in World 1.

Your goal: prove that every number is its own GCD.
"

/-- `myGcd n n = n`: a number is its own greatest common divisor. -/
TheoremDoc myGcd_self as "myGcd_self"

Statement myGcd_self (n : Nat) : myGcd n n = n := by
  Hint "Split on whether `n = 0` or `n = k + 1` with `cases n`."
  cases n with
  | zero => simp [myGcd]
  | succ n =>
    Hint "`simp [myGcd, Nat.mod_self]` should close this. `Nat.mod_self` says `n % n = 0`."
    simp [myGcd, Nat.mod_self]

Conclusion "
`Nat.mod_self` rewrites `(n+1) % (n+1)` to `0`, turning the recursive call into
the base case `myGcd (n+1) 0 = n+1`. Because Lean verified termination up front,
this equational reasoning is unconditionally valid.

Next: a brand-new recursive function — division by repeated subtraction.
"

/-- `n % n = 0` for any natural number. -/
TheoremDoc Nat.mod_self as "Nat.mod_self"

NewTheorem myGcd_self Nat.mod_self
