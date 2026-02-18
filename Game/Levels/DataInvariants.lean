import Game.Levels.DataInvariants.L01_IsBST
import Game.Levels.DataInvariants.L02_CheckBST
import Game.Levels.DataInvariants.L03_InsertLeaf
import Game.Levels.DataInvariants.L04_BoundsInsert
import Game.Levels.DataInvariants.L05_InsertBST
import Game.Levels.DataInvariants.L06_BSTSet

World "DataInvariants"
Title "Data Invariants"

Introduction "**World 6: Data Invariants**

A data structure is only useful if its **invariant** holds after every operation.
A binary search tree must stay ordered after every insert. A sorted list must
stay sorted after every addition.

In this world you will:
- Define the BST invariant (`IsBST`) using bound predicates
- Prove that `bstInsert` preserves the invariant
- Bundle everything into `BSTSet` — a verified BST type

The key insight: once you prove an operation preserves an invariant, the
compiler enforces it forever. No runtime check needed."
