import Game.Levels.AutomationPower.L01_SimpAll
import Game.Levels.AutomationPower.L02_SimpAttr
import Game.Levels.AutomationPower.L03_Grind
import Game.Levels.AutomationPower.L04_MapAppend
import Game.Levels.AutomationPower.L05_FilterPartition
import Game.Levels.AutomationPower.L06_GrindBST
import Game.Levels.AutomationPower.L07_FilterMap

World "AutomationPower"
Title "Automation Power"

Introduction "
Welcome to **World 3: Automation Power**!

You've proven programs correct one tactic at a time. Now we hand more
work to Lean's automation machinery — the same proofs that took five
lines before will often collapse to one or two.

**New tools in this world**:

- **`simp_all`** — like `simp`, but also rewrites using every hypothesis
  in the context. The induction hypothesis becomes automatic.
- **`@[simp]`** — an *attribute* that marks a theorem as a simplification
  rule. After tagging the equations of `myMap` with `@[simp]`, plain
  `simp` knows about them everywhere — no need to write `simp [myMap]`.
- **`grind`** — an automated prover combining equality reasoning and
  arithmetic. Feed it hints with `grind [lemma, ...]` and it hunts for
  a proof automatically.

You'll revisit `myMap`, `myFilter`, and the BST from World 2 — and
prove brand-new theorems about them with far less effort.
"
