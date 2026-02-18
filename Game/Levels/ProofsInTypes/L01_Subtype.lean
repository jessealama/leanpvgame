import Game.Levels.AutomationPower.L07_FilterMap

World "ProofsInTypes"
Level 1

Title "Subtypes: A Value With a Proof Inside"

Introduction "
In Lean, `{n : Nat // P n}` is a **subtype** — a type whose values are pairs `⟨n, h⟩`
where `n : Nat` and `h : P n`. The proof `h` is packed directly inside the value.

For example:
```lean
abbrev EvenNat := {n : Nat // n % 2 = 0}
```
A value of type `EvenNat` is guaranteed to be even — not by a runtime check, but by its type.

```lean
-- This compiles: 4 is even
example : EvenNat := ⟨4, by omega⟩

-- This is a type error: 3 is not even
-- example : EvenNat := ⟨3, by omega⟩  -- omega can't prove 3 % 2 = 0
```

The compiler is now the gatekeeper. To prove `n + n` is always even, use `omega`.
"

abbrev EvenNat := {n : Nat // n % 2 = 0}

/-- `(n + n) % 2 = 0` for all `n` -/
TheoremDoc double_even as "double_even"

Statement double_even : ∀ (n : Nat), (n + n) % 2 = 0 := by
  Hint "`omega` closes pure arithmetic goals."
  intro n; omega

Conclusion "
The proof is the membership certificate. No certificate, no value.

`double_even n` is the proof we'd pack into `⟨n + n, double_even n⟩ : EvenNat`.
"

/-- Supply a witness for an existential goal: `use expr` closes `⊢ ∃ x, P x` when `P expr` holds. -/
TacticDoc use
NewTactic use
/-- Subtype of even natural numbers: `{n : Nat // n % 2 = 0}` -/
DefinitionDoc EvenNat as "EvenNat"
NewDefinition EvenNat
