import Game.Levels.AutomationPower.L07_FilterMap

World "TheGrinder"
Level 1

Title "Congruence Closure: Equal Inputs, Equal Outputs"

Introduction "
**Welcome to The Grinder — your advanced `grind` dojo.**

You learned `grind [def]` in World 3: pass a definition hint and let `grind` close the goal.
Here we go deeper. This world has six levels, each unlocking a new `grind` capability.

First: `grind` without any hints at all.

`grind` has a built-in **congruence closure** engine. Given equalities in the context,
it automatically derives all consequences — including function application:

> If `a = b`, then `f a = f b` for any function `f`.

This rule chains: if `id1 = keyId` and `id2 = keyId`, then `id1 = id2`,
so `hashFn id1 = hashFn id2`.

**The scenario**: two software components produce IDs that must hash to the same bucket.
You're given that both IDs equal the same canonical `keyId`. Prove the hash values match.
"

/-- Equal inputs to a hash function produce equal outputs. -/
TheoremDoc hash_collision_free as "hash_collision_free"

Statement hash_collision_free (hashFn : Nat → Nat) (id1 id2 keyId : Nat)
    (h1 : id1 = keyId) (h2 : id2 = keyId) : hashFn id1 = hashFn id2 := by
  Hint "`grind` needs no hints here. It tracks `id1 = keyId` and `id2 = keyId`,
  merges all three into one equivalence class, then applies congruence:
  equal inputs to `hashFn` give equal outputs."
  grind

Conclusion "
`grind` merged `id1`, `id2`, and `keyId` into one equivalence class, then
applied the congruence rule `a = b → f a = f b` — all automatically.

Congruence closure is the foundation of grind's equality reasoning. Any chain of
equalities in the context is automatically exploited.
"
