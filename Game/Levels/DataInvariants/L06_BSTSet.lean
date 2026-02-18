import Game.Levels.DataInvariants.L05_InsertBST

World "DataInvariants"
Level 6

Title "The Verified BST"

Introduction "
Time to bundle everything into a **verified type**, just like `SortedList`
from World 4.

```lean
structure BSTSet where
  tree : Tree Nat
  valid : IsBST tree
```

A `BSTSet` is a `Tree Nat` paired with a proof that it satisfies the BST
invariant. You cannot construct an invalid BST — the type system prevents it.

We also define:
```lean
def BSTSet.empty : BSTSet := ⟨.leaf, by simp⟩

def BSTSet.insert (x : Nat) (s : BSTSet) : BSTSet :=
  ⟨bstInsert x s.tree, isBST_bstInsert x s.tree s.valid⟩
```

`BSTSet.insert` uses `isBST_bstInsert` (your theorem from Level 5!) to prove
the result is still a valid BST.

For the final proof: show that the inserted element can always be found.
"

structure BSTSet where
  tree : Tree Nat
  valid : IsBST tree

def BSTSet.empty : BSTSet := ⟨.leaf, by simp⟩

def BSTSet.insert (x : Nat) (s : BSTSet) : BSTSet :=
  ⟨bstInsert x s.tree, isBST_bstInsert x s.tree s.valid⟩

/-- After inserting `x`, membership lookup finds `x`. -/
TheoremDoc bstset_insert_member as "bstset_insert_member"

Statement bstset_insert_member (x : Nat) (s : BSTSet) :
    bstMember x (BSTSet.insert x s).tree = true := by
  Hint "Unfold `BSTSet.insert` to reveal `bstInsert`, then use `member_after_insert`
  from World 2.

  Try `exact member_after_insert x s.tree`."
  exact member_after_insert x s.tree

Conclusion "
Congratulations — you have completed **World 6: Data Invariants**!

You defined the BST invariant (`IsBST`) and proved that `bstInsert` preserves it.
Then you bundled the tree and its proof into `BSTSet` — a type where the invariant
is **enforced by construction**.

What you built:
- `AllLt`, `AllGt` — bound predicates for subtrees
- `IsBST` — the full BST ordering invariant
- `allLt_bstInsert` — bounds survive insertion
- `allGt_bstInsert` — symmetric bound preservation
- `isBST_bstInsert` — **the main theorem**: insertion preserves BST
- `BSTSet` — a verified BST type, closed under `insert`

The same pattern works for *any* data structure with an invariant:
1. Define the invariant as a predicate
2. Prove each operation preserves it
3. Bundle the data and proof into a structure

No runtime check. No test suite. The compiler guarantees correctness for all inputs.

Onward to **World 7: Pre/Post Conditions**!
"

/-- A tree paired with a proof of the BST invariant. -/
DefinitionDoc BSTSet as "BSTSet"
/-- The empty BST. -/
DefinitionDoc BSTSet.empty as "BSTSet.empty"
/-- Insert into a BST, preserving the invariant. -/
DefinitionDoc BSTSet.insert as "BSTSet.insert"
NewDefinition BSTSet BSTSet.empty BSTSet.insert
