import Game.Levels.ImperativeIntro.L01_Swap
import Game.Levels.ImperativeIntro.L02_Sum
import Game.Levels.ImperativeIntro.L03_AllPositive
import Game.Levels.ImperativeIntro.L04_LinearSearch
import Game.Levels.ImperativeIntro.L05_FindMax
import Game.Levels.ImperativeIntro.L06_CountOcc

World "ImperativeIntro"
Title "Imperative Intro"

Introduction "
**Welcome to Imperative Verification!**

So far you have proved properties of *pure* functions.
Now we verify programs that use **mutable state** and **loops** — code that *looks*
imperative while remaining 100% verified.

## The workflow

Every imperative proof follows the same three steps:

1. **Write the spec** as a Hoare triple: `⦃⌜precondition⌝⦄ prog ⦃⇓ r => ⌜postcondition r⌝⦄`
2. **Call `mvcgen [prog]`** to generate verification conditions (VCs) from the do-block.
3. **Supply a loop invariant** and close VCs with `grind`.

For a loop `for x in a do ...`, the invariant is stated over the *loop cursor* `xs`
(tracking which elements have been processed) and the current mutable variables:
```lean
mvcgen [myFunc] invariants
· ⇓⟨xs, myVar⟩ => ⌜<relationship between myVar and xs.prefix>⌝
with grind
```

The key insight: **the invariant is usually the specification restricted to the prefix
seen so far**.

Let's verify some programs!
"
