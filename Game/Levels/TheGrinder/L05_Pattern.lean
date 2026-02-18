import Game.Levels.TheGrinder.L04_GrindFwd

World "TheGrinder"
Level 5

Title "@[grind]: Registering Lemmas for E-matching"

Introduction "
The final annotation: `@[grind]` (without `=` or `→`) registers a theorem for
grind's **E-matching** engine.

E-matching is pattern-based: grind watches for terms matching the LHS of your theorem
and instantiates it automatically. It's how grind handles universally quantified lemmas
about recursive functions.

```lean
@[grind] theorem myMap_len_eq (f : α → β) (l : List α) :
    (myMap f l).length = l.length := by
  induction l with
  | nil          => simp [myMap]
  | cons x xs ih => simp [myMap, ih]
```

With this annotation, whenever grind's E-matching engine sees `(myMap _ _).length`,
it instantiates `myMap_len_eq` automatically.

**The challenge**: prove that mapping twice preserves length.

```lean
map_map_len (f g : Nat → Nat) (l : List Nat) :
    (myMap f (myMap g l)).length = l.length
```

E-matching fires twice:
1. `(myMap f (myMap g l)).length` matches → `= (myMap g l).length`
2. `(myMap g l).length` matches → `= l.length`

Transitivity gives the result.
"

@[grind] theorem myMap_len_eq (f : α → β) (l : List α) :
    (myMap f l).length = l.length := by
  induction l with
  | nil          => simp [myMap]
  | cons x xs ih => simp [myMap, ih]

/-- `(myMap f (myMap g l)).length = l.length` -/
TheoremDoc map_map_len as "map_map_len"

Statement map_map_len (f g : Nat → Nat) (l : List Nat) :
    (myMap f (myMap g l)).length = l.length := by
  Hint "Just `grind`. The `@[grind]` annotation on `myMap_len_eq` makes E-matching
  fire twice — once for the outer `myMap f ...` and once for the inner `myMap g l`."
  grind

Conclusion "
`@[grind]` registered `myMap_len_eq` for E-matching.
Grind instantiated it twice and used transitivity automatically.

Summary of grind annotations:
- `@[grind =]` — equations: rewrite LHS → RHS automatically
- `@[grind →]` — implications: fire whenever premise holds
- `@[grind]` — universally quantified theorems: E-match and instantiate

One level to go. Let's combine them all.
"

/-- `(myMap f l).length = l.length` (registered for grind E-matching) -/
TheoremDoc myMap_len_eq as "myMap_len_eq"
NewTheorem myMap_len_eq
