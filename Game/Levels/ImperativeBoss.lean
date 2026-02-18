import Game.Levels.ImperativeBoss.L01_Instr
import Game.Levels.ImperativeBoss.L02_Run
import Game.Levels.ImperativeBoss.L03_Compile
import Game.Levels.ImperativeBoss.L04_RunAppend
import Game.Levels.ImperativeBoss.L05_CompileNum
import Game.Levels.ImperativeBoss.L06_CompileAdd
import Game.Levels.ImperativeBoss.L07_CompileMul
import Game.Levels.ImperativeBoss.L08_CompileCorrect
import Game.Levels.ImperativeBoss.L09_Exec
import Game.Levels.ImperativeBoss.L10_Victory

World "ImperativeBoss"
Title "Imperative Boss"

Introduction "**World 9: Imperative Boss — A Verified Compiler**

The final challenge: build a **verified compiler** from arithmetic expressions to
a stack machine.

You will:
1. Define a stack machine instruction set and executor
2. Write a compiler from `Expr` (World 2) to stack instructions
3. Prove compiler correctness: compiled code computes `eval`
4. Verify an imperative executor using `mvcgen`

This capstone ties together everything — induction, `simp` lemmas, `generalizing`,
and Hoare-logic verification — into one coherent verified compilation pipeline."
