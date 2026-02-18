import Game.Levels.ProofsInTypes.L03_Fin

World "ProofsInTypes"
Level 4

Title "Safe Head: Proof-Carrying Functions"

Introduction "
`List.head?` returns `Option α` — safe, but forces callers to handle `none` everywhere,
even when they *know* the list is non-empty.

Instead, we can demand a **proof** of non-emptiness as an argument:

```lean
def safeHead {α : Type} (l : List α) (_ : l ≠ []) : α :=
  match l with
  | x :: _ => x
  | []      => by contradiction
```

Calling `safeHead [] h` is a **type error** — you cannot provide a proof of `[] ≠ []`.
The function returns `α` directly; no `Option` unwrapping needed.

The statement below says `safeHead` on a cons list returns the head element. Because
`safeHead` reduces definitionally, the proof is trivial.
"

def safeHead {α : Type} (l : List α) (_ : l ≠ []) : α :=
  match l with
  | x :: _ => x
  | []      => by contradiction

/-- `safeHead (x :: xs) h = x` -/
TheoremDoc safeHead_cons as "safeHead_cons"

Statement safeHead_cons : ∀ {α : Type} (x : α) (xs : List α),
    safeHead (x :: xs) (List.cons_ne_nil x xs) = x := by
  Hint "The definition reduces definitionally. Try `rfl`."
  intro α x xs; rfl

Conclusion "
`rfl` works because `safeHead (x :: xs) _` *definitionally equals* `x`.
The compiler verified the precondition; we never needed to handle `none`.
"

/-- Return the head of a non-empty list, with non-emptiness proved at call site. -/
DefinitionDoc safeHead as "safeHead"
NewDefinition safeHead
