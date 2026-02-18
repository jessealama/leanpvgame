import Game.Levels.Termination.L06_Victory

World "Termination"
Title "Termination"

Introduction "
**Welcome to World 5: Termination!**

Every function in this game so far used *structural* recursion — shrinking a
list or a number constructor by constructor. Lean accepted those automatically.

Real algorithms often recurse differently:
- Division subtracts until zero (measure: the dividend)
- Logarithm halves until below 2 (measure: the value)
- Merge recurses on two shrinking lists at once (measure: combined length)

Lean 4 handles all of these with two declarations:
```lean
termination_by <expression>   -- the measure that gets smaller
decreasing_by <tactic>        -- proof that it strictly decreases
```

Once Lean accepts the termination proof, the function is **total** — you can
reason about it freely, for any input, forever.

In each level, the function and its termination argument are already written.
Your job: prove a property *about* the function, using the same structure that
makes it terminate.
"
