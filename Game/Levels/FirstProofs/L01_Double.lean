import Game.Metadata

World "FirstProofs"
Level 1

Title "Double or Nothing"

Introduction "Welcome to the **Program Verification Game**!

In this game you will write mathematical proofs to verify that programs are correct.
The Lean proof assistant checks every step — there is no way to cheat.

Your first program:
```
def double (n : Nat) : Nat := n + n
```

`double` is supposed to double its input.
Prove that it always does — for **every** natural number `n`."

def double (n : Nat) : Nat := n + n

/-- `double n = n + n` for all `n`. -/
TheoremDoc double_correct as "double_correct"

Statement double_correct : ∀ (n : Nat), double n = n + n := by
  Hint "Start with `intro n` to bring the variable into scope."
  intro n
  Hint "Now `simp [double]` will unfold the definition and close the goal."
  simp [double]

Conclusion "Lean accepted your proof!

`simp [double]` unfolded the definition of `double` and closed the goal by reflexivity.

You have formally verified your first program. Welcome to program verification!"

NewTactic rfl simp intro exact
/-- `double n = n + n` -/
DefinitionDoc double as "double"
NewDefinition double
