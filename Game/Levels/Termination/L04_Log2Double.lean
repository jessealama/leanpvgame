import Game.Levels.Termination.L03_MyLog2

World "Termination"
Level 4

Title "The Doubling Law"

Introduction "
Every logarithm satisfies: `log(2 · n) = log(n) + 1`.

For our integer `myLog2`, this becomes:

```
myLog2 (2 * n) = myLog2 n + 1   (when n > 0)
```

You have `myLog2_ge_two` to unfold one step (since `2 * n ≥ 2` when `n > 0`),
and `Nat.mul_div_cancel_left` which says `k * m / k = m` when `0 < k`.

Your proof is two lines: one `rw` and one `simp`.
"

/-- The doubling law: `myLog2 (2 * n) = myLog2 n + 1` for positive `n`. -/
TheoremDoc myLog2_double as "myLog2_double"

Statement myLog2_double (n : Nat) (h : 0 < n) : myLog2 (2 * n) = myLog2 n + 1 := by
  Hint "The argument `2 * n ≥ 2` follows from `h`. Use `rw [myLog2_ge_two (by omega)]`."
  rw [myLog2_ge_two (by omega)]
  Hint "`Nat.mul_div_cancel_left` says `k * m / k = m`. Try `simp [Nat.mul_div_cancel_left]`."
  simp

Conclusion "
`rw [myLog2_ge_two (by omega)]` replaced `myLog2 (2 * n)` with `myLog2 (2 * n / 2) + 1`.
Then `simp [Nat.mul_div_cancel_left]` simplified `2 * n / 2` to `n`.

This is the algebraic identity you'd expect from any logarithm — and it follows
directly from the recursive definition and two standard lemmas.
"

/-- `k * m / k = m` when `0 < k`. -/
TheoremDoc Nat.mul_div_cancel_left as "Nat.mul_div_cancel_left"

NewTheorem myLog2_double Nat.mul_div_cancel_left
