import Game.Levels.PurePrograms.L03_MyFoldr

World "PurePrograms"
Level 4

Title "The Termination Wall"

Introduction "
Until now, every recursive function you've seen has been **structurally recursive**:
each recursive call is on a smaller piece of the input (a tail, a subtree).
Lean accepts these automatically.

But what about this?

```lean
def half (n : Nat) : Nat :=
  if n < 2 then 0 else 1 + half (n - 2)
```

Lean **rejects** this without a termination proof! The recursive call is on `n - 2`,
not a structural predecessor of `n`. Lean can't automatically verify that `n - 2 < n`.

We fix this with a **termination measure**:

```lean
def half (n : Nat) : Nat :=
  if n < 2 then 0 else 1 + half (n - 2)
termination_by n
decreasing_by omega
```

`termination_by n` says: *the measure is just `n` itself*.
`decreasing_by omega` says: *trust `omega` to prove `n - 2 < n` when `¬(n < 2)`*.

**Your goal** has two parts:
1. Verify concrete values of `half` (using `native_decide`).
2. Prove the key arithmetic fact that makes `decreasing_by omega` work: when `n ≥ 2`, we have `n - 2 < n`.

The second part is exactly the inequality `omega` closes automatically — try it manually!
"

def half (n : Nat) : Nat :=
  if n < 2 then 0 else 1 + half (n - 2)
termination_by n
decreasing_by omega

/-- `half 0 = 0`, `half 1 = 0`, and when `n ≥ 2`, `n - 2 < n`. -/
TheoremDoc half_correct as "half_correct"

Statement half_correct :
    (half 0 = 0 ∧ half 1 = 0 ∧ half 4 = 2 ∧ half 10 = 5) ∧
    ∀ (n : Nat), n ≥ 2 → n - 2 < n := by
  constructor
  · native_decide
  · intro n h
    Hint "The second part is the exact inequality `decreasing_by omega` proves
automatically. Can you prove it manually?"
    omega

Conclusion "
You've hit the termination wall — and climbed it!

- **Structural recursion**: Lean accepts it for free (lists, trees).
- **Non-structural recursion**: supply `termination_by <measure>` and `decreasing_by <tactic>`.

`omega` is powerful enough to discharge most arithmetic termination obligations.
You'll see this pattern again in World 4.
"

/-- Integer division by 2, defined by well-founded recursion. -/
DefinitionDoc half as "half"
NewDefinition half
