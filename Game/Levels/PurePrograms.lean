import Game.Levels.PurePrograms.L01_MyMap
import Game.Levels.PurePrograms.L02_MyFilter
import Game.Levels.PurePrograms.L03_MyFoldr
import Game.Levels.PurePrograms.L04_Half
import Game.Levels.PurePrograms.L05_Tree
import Game.Levels.PurePrograms.L06_BST
import Game.Levels.PurePrograms.L07_Expr

World "PurePrograms"
Title "Pure Programs"

Introduction "
Welcome to **World 2: Pure Programs**!

All code here is *pure* — no mutable state, no side effects.
But purity doesn't mean simple: you'll build polymorphic list operations,
a binary search tree, and a tiny expression evaluator — all verified by Lean.

Along the way you'll hit the **termination wall**: Lean demands a proof that
every recursive function eventually stops.

- **Structural recursion** (on `List`, on `Tree`): Lean accepts it automatically.
- **Non-structural recursion**: you must supply a measure with `termination_by`
  and prove it decreases with `decreasing_by`.

You already saw this in World 1 with `myGcd`. Here you'll see it again — and
understand exactly why Lean insists on it.
"
