import Game.Levels.Termination.L01_GcdSelf

World "Termination"
Level 2

Title "Division by Repeated Subtraction"

Introduction "
Here is a function that computes `x / y` by repeatedly subtracting `y` from `x`:

```lean
def myDiv (x y : Nat) : Nat :=
  if 0 < y ∧ y ≤ x then myDiv (x - y) y + 1 else 0
termination_by x
decreasing_by omega
```

The termination measure is `x`. When `y ≤ x` and `0 < y`, subtracting `y`
gives `x - y < x`, so the measure strictly decreases. `omega` verifies this.

Two key facts follow directly from the definition:
- **Base case**: `myDiv 0 y = 0` (the condition `0 < y ∧ y ≤ 0` is always false)
- **Step case**: when `0 < y` and `y ≤ x`, `myDiv x y = myDiv (x - y) y + 1`

Your goal: prove that dividing a positive number by itself gives 1.

**Hint**: Split into cases on `n`. The `zero` case follows from the hypothesis.
For the `succ` case, `simp [myDiv]` unfolds the definition and closes the goal.
"

def myDiv (x y : Nat) : Nat :=
  if 0 < y ∧ y ≤ x then myDiv (x - y) y + 1 else 0
termination_by x
decreasing_by omega

/-- `myDiv n n = 1` for positive `n`: dividing a number by itself gives 1. -/
TheoremDoc myDiv_self as "myDiv_self"

Statement myDiv_self (n : Nat) (h : 0 < n) : myDiv n n = 1 := by
  Hint "Use `cases n with` to split on whether `n = 0` or `n = k + 1`."
  cases n with
  | zero => omega
  | succ n =>
    Hint "`simp [myDiv]` unfolds the definition. It reduces `myDiv (n+1) (n+1)`
to `myDiv 0 (n+1) + 1`, then `myDiv 0 (n+1)` to `0` (the condition `n+1 ≤ 0`
is false), giving `0 + 1 = 1`."
    simp [myDiv]

Conclusion "
The proof mirrors the termination argument:
- **Base case** (`n = 0`): impossible since `h : 0 < 0`, so `omega` closes it.
- **Step case** (`n = k+1`): `simp [myDiv]` unfolds one step, uses `k+1 - (k+1) = 0`,
  then unfolds again at `myDiv 0 (k+1)` where the condition `k+1 ≤ 0` is false.

The `simp [myDiv]` terminates here because the RHS is just `1` — there is no
`myDiv` on the right side for simp to endlessly expand.
"

/-- Division by repeated subtraction. -/
DefinitionDoc myDiv as "myDiv"
NewDefinition myDiv
NewTheorem myDiv_self
