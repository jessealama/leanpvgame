import Game.Levels.PrePost.L01_StackContract

World "PrePost"
Level 2

Title "Lookup After Insert"

Introduction "
Next: a simple key-value map, implemented as an association list.

```lean
def mapInsert (k v : Nat) (m : List (Nat × Nat)) : List (Nat × Nat) :=
  (k, v) :: m

def mapLookup (k : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (k', v) :: rest => if k == k' then some v else mapLookup k rest
```

The contract: **looking up a key immediately after inserting it returns the
inserted value**.
"

def mapInsert (k v : Nat) (m : List (Nat × Nat)) : List (Nat × Nat) :=
  (k, v) :: m

def mapLookup (k : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (k', v) :: rest => if k == k' then some v else mapLookup k rest

/-- Looking up a key after inserting it returns the inserted value. -/
TheoremDoc lookup_after_insert as "lookup_after_insert"

Statement lookup_after_insert (k v : Nat) (m : List (Nat × Nat)) :
    mapLookup k (mapInsert k v m) = some v := by
  Hint "Try `simp [mapInsert, mapLookup]`."
  simp [mapInsert, mapLookup]

Conclusion "
Again, one line! `simp` unfolded `mapInsert` to `(k, v) :: m`, then unfolded
`mapLookup` at the cons case, saw `k == k` (which simplifies to `true`), and
closed the goal.

These simple contracts — *insert then lookup*, *push then pop* — are the
building blocks of verified data structure libraries.
"

/-- Insert a key-value pair at the front of an association list. -/
DefinitionDoc mapInsert as "mapInsert"
/-- Look up a key in an association list. -/
DefinitionDoc mapLookup as "mapLookup"
NewDefinition mapInsert mapLookup
