import Game.Levels.ProofsInTypes.L01_Subtype

World "ProofsInTypes"
Level 2

Title "Extracting the Packed Proof"

Introduction "
Every subtype value carries two pieces:
- `.val` (or `.1`): the underlying value
- `.property` (or `.2`): the proof

For `e : EvenNat`:
- `e.val : Nat` — the number itself
- `e.property : e.val % 2 = 0` — the proof it's even

The type system **guarantees** this proof exists. You cannot construct an `EvenNat` without
providing a proof of evenness.
"

/-- For any `e : EvenNat`, `e.val % 2 = 0` -/
TheoremDoc even_val as "even_val"

Statement even_val : ∀ (e : EvenNat), e.val % 2 = 0 := by
  Hint "Try `exact e.2` or `exact e.property`."
  intro e; exact e.2

Conclusion "
`.val` gives the data; `.property` gives the proof. Both are always present.
"
