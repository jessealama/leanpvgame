import Game.Levels.TheGrinder.L06_Victory

World "TheGrinder"
Title "The Grinder"

Introduction "
**Welcome to The Grinder — your advanced `grind` dojo.**

In World 3 you learned `grind [def]`: pass a definition hint and let `grind` close the goal.
Here we go deeper: teach `grind` your own rules so it needs *no* hints at all.

`grind` is an automated prover with three cooperating engines:

- **Congruence closure** — derives equalities from equalities (levels 1–2)
- **Linear arithmetic** — like `omega`, integrated with the other engines (level 2)
- **E-matching** — instantiates annotated lemmas when patterns appear (levels 3–5)

And three annotation tools you'll master here:

- `@[grind =]` — your equation becomes an automatic rewrite rule (level 3)
- `@[grind →]` — your implication becomes an automatic forward rule (level 4)
- `@[grind]` — your theorem is registered for E-matching instantiation (level 5)

All examples reuse definitions from Worlds 1–3 (`double`, `myMap`, `myFilter`).

Annotate your invariants once. Let `grind` verify any consequence — forever.
"
