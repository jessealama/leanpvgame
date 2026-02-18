import Game.Levels.Termination.L02_MyDiv

World "Termination"
Level 3

Title "Logarithm by Repeated Halving"

Introduction "
Integer base-2 logarithm, computed by halving:

```lean
def myLog2 (n : Nat) : Nat :=
  match n with
  | 0 | 1  => 0
  | n + 2  => myLog2 ((n + 2) / 2) + 1
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)
```

The match makes the cases explicit: `0` and `1` are base cases (result 0);
any `n ≥ 2` (written `n + 2`) halves and recurses. `Nat.div_lt_self` certifies
that `(n+2)/2 < n+2`, so the measure `n` strictly decreases.

Two helper theorems are available:

```lean
theorem myLog2_lt_two {n : Nat} (h : n < 2)  : myLog2 n = 0
theorem myLog2_ge_two {n : Nat} (h : 2 ≤ n)  : myLog2 n = myLog2 (n / 2) + 1
```

Use them to prove: if `n ≥ 2`, then `myLog2 n` is positive.
"

def myLog2 (n : Nat) : Nat :=
  match n with
  | 0 | 1 => 0
  | n + 2 => myLog2 ((n + 2) / 2) + 1
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

@[simp] theorem myLog2_lt_two {n : Nat} (h : n < 2) : myLog2 n = 0 := by
  cases n with
  | zero => simp [myLog2]
  | succ n => cases n with
    | zero => simp [myLog2]
    | succ n => omega

@[simp] theorem myLog2_ge_two {n : Nat} (h : 2 ≤ n) : myLog2 n = myLog2 (n / 2) + 1 := by
  cases n with
  | zero => omega
  | succ n => cases n with
    | zero => omega
    | succ n => simp [myLog2]; congr 1; omega

/-- `myLog2 n > 0` whenever `n ≥ 2`. -/
TheoremDoc myLog2_pos as "myLog2_pos"

Statement myLog2_pos (n : Nat) (h : 2 ≤ n) : 0 < myLog2 n := by
  Hint "Rewrite `myLog2 n` using `myLog2_ge_two h`."
  rw [myLog2_ge_two h]
  Hint "`omega` closes `0 < myLog2 (n / 2) + 1` since any Nat plus 1 is positive."
  omega

Conclusion "
After `rw [myLog2_ge_two h]`, the goal became `0 < myLog2 (n / 2) + 1`.
Any natural number plus 1 is positive, which `omega` handles in one step.

Notice how the termination measure (`n`) guided the proof structure:
the interesting case is `n ≥ 2`, exactly when `myLog2` recurses.
"

/-- Integer base-2 logarithm by repeated halving. -/
DefinitionDoc myLog2 as "myLog2"
NewDefinition myLog2
/-- `myLog2 n = 0` when `n < 2`. -/
TheoremDoc myLog2_lt_two as "myLog2_lt_two"

/-- `myLog2 n = myLog2 (n / 2) + 1` when `2 ≤ n`. -/
TheoremDoc myLog2_ge_two as "myLog2_ge_two"

NewTactic rw
NewTheorem myLog2_lt_two myLog2_ge_two myLog2_pos
