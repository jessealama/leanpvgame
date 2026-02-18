import Game.Levels.FirstProofs.L01_Double

World "FirstProofs"
Level 2

Title "Even Numbers"

Introduction "A natural number is **even** if it is divisible by 2.
We can express this as a proposition in Lean:
```
def isEven (n : Nat) : Prop := n % 2 = 0
```

In the previous level, you proved that `double n = n + n`.
Now prove that doubling any number always produces an even number.

*Tip*: `simp [isEven, double]` can unfold both definitions at once,
then `omega` handles the arithmetic."

def isEven (n : Nat) : Prop := n % 2 = 0

/-- `double n` is always even. -/
TheoremDoc double_is_even as "double_is_even"

Statement double_is_even : ∀ (n : Nat), isEven (double n) := by
  Hint "Start with `intro n` to introduce the variable."
  intro n
  Hint "Try `simp [isEven, double]` to unfold both definitions."
  simp [isEven, double]
  Hint "The remaining goal is an arithmetic fact. Try `omega`."
  omega

Conclusion "`simp [isEven, double]` unfolded both definitions, turning the goal into
`(n + n) % 2 = 0`. Then `omega` — Lean's built-in linear arithmetic solver —
finished the proof automatically.

`omega` is incredibly powerful: it can prove any goal that follows from linear
arithmetic over integers and natural numbers."

NewTactic omega
/-- `isEven n ↔ n % 2 = 0` -/
DefinitionDoc isEven as "isEven"
NewDefinition isEven
