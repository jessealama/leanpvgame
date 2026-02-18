import Game.Levels.FirstProofs.L06_Coprime

World "FirstProofs"
Level 7

Title "Is This Prime?"

Introduction "You've built and verified the Euclidean algorithm. Now use it to verify
a **primality checker** built from `myGcd`!

A number `n` is prime if `n ≥ 2` and every number `d` in `[2, n-1]`
is coprime with `n`:
```
def isPrime (n : Nat) : Bool :=
  n ≥ 2 &&
  ((List.range n).drop 2).all (fun d => myGcd n d == 1)
```

Prove that 2, 3, and 5 are prime, and that 4 is not:
```
isPrime 2 = true ∧ isPrime 3 = true ∧ isPrime 4 = false ∧ isPrime 5 = true
```

*Tip*: All four values are **computable** — try `native_decide` to evaluate them instantly."

def isPrime (n : Nat) : Bool :=
  n ≥ 2 &&
  ((List.range n).drop 2).all (fun d => myGcd n d == 1)

/-- `isPrime 2 = true`, `isPrime 3 = true`, `isPrime 4 = false`, `isPrime 5 = true` -/
TheoremDoc isPrime_small as "isPrime_small"

Statement isPrime_small :
    isPrime 2 = true ∧ isPrime 3 = true ∧ isPrime 4 = false ∧ isPrime 5 = true := by
  Hint "All of these are concrete computations. Try `native_decide`!"
  native_decide

Conclusion "`native_decide` compiled `isPrime` to native code and **evaluated** each value
and verify the result. Since `isPrime` is a computable function (using `myGcd`),
Lean can do this automatically — no manual proof steps needed.

The same `myGcd` you proved correct in levels 4–5 powers this verification.
This is **program verification in action**: prove your building blocks correct,
then compose them into larger verified programs.

**Congratulations — you've completed World 1!**

Continue to World 2 to learn how to write complete functional specifications."

NewTactic decide native_decide
/-- `n` is prime iff `n > 1` and it is coprime with all `k` in `[2, n-1]`. -/
DefinitionDoc isPrime as "isPrime"
NewDefinition isPrime
