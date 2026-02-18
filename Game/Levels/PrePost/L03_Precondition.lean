import Game.Levels.PrePost.L02_MapContract

World "PrePost"
Level 3

Title "Preconditions Save Lives"

Introduction "
So far our contracts had no preconditions — they held for *all* inputs.
But some operations are only valid under certain assumptions.

Division by zero is undefined. We can encode this as a **precondition**:

```lean
def safeMod (n d : Nat) (h : d ≠ 0) : Nat := n % d
```

The caller must supply a proof `h : d ≠ 0` to call `safeMod`. In exchange,
the function guarantees the result is less than the divisor.
"

def safeMod (n d : Nat) (h : d ≠ 0) : Nat := n % d

/-- `safeMod n d h` is strictly less than `d`. -/
TheoremDoc safeMod_lt as "safeMod_lt"

Statement safeMod_lt (n d : Nat) (h : d ≠ 0) : safeMod n d h < d := by
  Hint "Unfold `safeMod` with `simp [safeMod]`, then use
  `exact Nat.mod_lt n (by omega)` to close the goal."
  simp [safeMod]
  exact Nat.mod_lt n (by omega)

Conclusion "
The precondition `d ≠ 0` made the proof possible — without it, the statement
would be false!

This is the essence of **design by contract**:
- The **precondition** says what the *caller* must guarantee.
- The **postcondition** says what the *function* will guarantee in return.

In Lean, preconditions are just hypotheses in the function's type. The type
checker enforces them at every call site — no runtime check needed.
"

/-- Safe modulo: requires a proof that the divisor is nonzero. -/
DefinitionDoc safeMod as "safeMod"
/-- `n % d < d` when `0 < d`. -/
TheoremDoc Nat.mod_lt as "Nat.mod_lt"

NewDefinition safeMod
NewTheorem Nat.mod_lt
