import Game.Levels.FirstProofs.L05_GcdStep

World "FirstProofs"
Level 6

Title "Coprime Numbers"

Introduction "Two numbers are **coprime** (or relatively prime) if their GCD equals 1.
This is a key concept in number theory and cryptography — for example,
RSA encryption requires finding large coprime numbers.

We define coprimality using `myGcd`:
```
def myCoprime (a b : Nat) : Prop := myGcd a b = 1
```

Prove that `myCoprime a b` is logically equivalent to `myGcd a b = 1`.

*Tip*: Use `constructor` to split the `↔` into two implications. Both directions
are symmetric, so you can use the **`<;>`** combinator to apply the same tactic to
all remaining goals at once:
```
constructor <;> intro h <;> exact h
```
reads as: split, then introduce the hypothesis in *every* subgoal, then close
*every* subgoal with `exact h`."

def myCoprime (a b : Nat) : Prop := myGcd a b = 1

/-- `myCoprime a b ↔ myGcd a b = 1` -/
TheoremDoc coprime_iff as "coprime_iff"

Statement coprime_iff : ∀ (a b : Nat), myCoprime a b ↔ myGcd a b = 1 := by
  Hint "Use `intro a b`, then `constructor <;> intro h <;> exact h`.
  Or split manually: `constructor`, then prove each direction with `intro h; exact h`."
  intro a b
  constructor <;> intro h <;> exact h

Conclusion "Both directions are proved by `exact h` — because `myCoprime a b` is
**defined as** `myGcd a b = 1`. They are literally the same proposition!

`constructor` splits a goal of the form `P ↔ Q` (or `P ∧ Q`) into separate subgoals.
The `<;>` combinator then applies the following tactic to **every** resulting goal.
So `constructor <;> intro h <;> exact h` means:
1. Split into two goals.
2. In each goal, introduce the hypothesis as `h`.
3. In each goal, close with `exact h`.

You'll see `<;>` often in later worlds — for example, `induction xs <;> simp_all`
applies `simp_all` to both the base case and the inductive case in one stroke."

NewTactic constructor
/-- `a` and `b` are coprime iff `myGcd a b = 1`. -/
DefinitionDoc myCoprime as "myCoprime"
NewDefinition myCoprime
