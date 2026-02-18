import Game.Levels.FirstProofs
import Game.Levels.PurePrograms
import Game.Levels.AutomationPower
import Game.Levels.TheGrinder
import Game.Levels.ProofsInTypes
import Game.Levels.Termination
import Game.Levels.DataInvariants
import Game.Levels.PrePost
import Game.Levels.ImperativeIntro
import Game.Levels.ImperativeBoss

Title "Program Verification Game"

Introduction "
# Welcome to the Program Verification Game!

In this game you will learn **formal program verification** — the art of
proving mathematical theorems about programs to guarantee they are correct.

You will use **Lean 4**, a proof assistant that checks every step of your reasoning.

## The Worlds

| # | World | Theme |
|---|-------|-------|
| 1 | **First Proofs** | Core tactics, GCD algorithm, primality |
| 2 | **Pure Programs** | Pure recursive programs + termination |
| 3 | **Automation Power** | simp_all, grind, and @[simp] |
| 3★ | **The Grinder** (optional) | Advanced grind: @[grind =], @[grind →], E-matching |
| 4 | **Proofs in Types** | Subtypes, Fin, proof-carrying functions |
| 5 | **Termination** | Proving programs always terminate |
| 6 | **Data Invariants** | Sorted lists, balanced trees, invariant maintenance |
| 7 | **Pre/Post Conditions** | Hoare-style contracts |
| 8 | **Imperative Intro** | Verifying mutable state and loops |
| 9 | **Imperative Boss** | Verified mini-compiler (capstone) |

Start with **World 1** to learn the basics!
"

Info "
## About this Game

**Program Verification Game** teaches formal program verification using Lean 4.

The curriculum covers an 8-world progression from basic functional proofs
through imperative verification with loop invariants.

**Version**: 0.2.0 (All 9 worlds playable)

**Source**: https://github.com/your-org/pvgame
"

Languages "en"
CaptionShort "Program Verification Game"
CaptionLong "Learn to formally verify programs using Lean 4, from basic proofs to imperative algorithms."

-- World dependency graph
Dependency FirstProofs → PurePrograms
Dependency PurePrograms → AutomationPower
Dependency AutomationPower → TheGrinder
Dependency AutomationPower → ProofsInTypes
Dependency AutomationPower → Termination
Dependency ProofsInTypes → DataInvariants
Dependency Termination → DataInvariants
Dependency DataInvariants → PrePost
Dependency PrePost → ImperativeIntro
Dependency ImperativeIntro → ImperativeBoss

MakeGame
