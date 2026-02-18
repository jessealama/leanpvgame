import Game.Levels.ProofsInTypes.L07_InsertSorted

World "ProofsInTypes"
Level 8

Title "Victory: The Proof-Carrying Insert"

Introduction "
The payoff: a `SortedList.insert` that **returns a `SortedList`**, not a bare `List Nat`.

```lean
def SortedList.insert (x : Nat) (sl : SortedList) : SortedList :=
  ⟨insertSorted x sl.data, insertSorted_sorted x sl.data sl.sorted⟩
```

The proof `insertSorted_sorted x sl.data sl.sorted` is baked into the return type.
You cannot call this function incorrectly, and its result is guaranteed sorted for
**all** inputs — verified once at compile time.

No unit test. No runtime assertion. No documentation that might drift. The type says it all.

First, a helper lemma: the inserted element is always in the result.
Use `obtain` to destructure hypotheses of the form `h : A ∧ B` into `⟨h1, h2⟩`.
"

theorem insertSorted_mem (x : Nat) (l : List Nat) : x ∈ insertSorted x l := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    simp only [insertSorted]
    by_cases hxy : x ≤ y
    · simp [hxy]
    · simp only [if_neg hxy]
      exact List.mem_cons_of_mem _ ih

def SortedList.insert (x : Nat) (sl : SortedList) : SortedList :=
  ⟨insertSorted x sl.data, insertSorted_sorted x sl.data sl.sorted⟩

/-- `x ∈ (SortedList.insert x sl).data` -/
TheoremDoc insert_mem as "insert_mem"

Statement insert_mem : ∀ (x : Nat) (sl : SortedList),
    x ∈ (SortedList.insert x sl).data := by
  Hint "Unfold `SortedList.insert`. The result's `.data` is `insertSorted x sl.data`.
  Then apply `insertSorted_mem`."
  intro x sl
  exact insertSorted_mem x sl.data

Conclusion "
World 4 complete! You've packed proofs into types:

- **EvenNat** — only even numbers can be constructed
- **Fin n** — indices that are provably in-bounds
- **safeHead** — a head function that cannot be called on empty lists
- **Sorted** — a predicate encoding a list's invariant
- **SortedList** — a type where sortedness is enforced at construction
- **SortedList.insert** — insertion that preserves sortedness, verified once for all time

Onward to World 5: Termination!
"

NewTactic obtain
/-- Insert a `Nat` into a `SortedList`, returning a `SortedList`. -/
DefinitionDoc SortedList.insert as "SortedList.insert"
NewDefinition SortedList.insert
/-- `x ∈ insertSorted x l` for any list `l` -/
TheoremDoc insertSorted_mem as "insertSorted_mem"
NewTheorem insertSorted_mem
