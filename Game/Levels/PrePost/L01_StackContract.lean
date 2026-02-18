import Game.Levels.DataInvariants.L06_BSTSet

World "PrePost"
Level 1

Title "Stack Push/Pop Cancellation"

Introduction "
Welcome to **Pre/Post Conditions**!

A **contract** for a function says what it *guarantees* (postcondition) given what
it may *assume* (precondition). In this world we will write and prove contracts for
increasingly interesting programs.

Let's start simple. Here is a stack, implemented as a list:

```lean
abbrev Stack (α : Type) := List α

def Stack.push (x : α) (s : Stack α) : Stack α := x :: s

def Stack.pop : Stack α → Option (α × Stack α)
  | [] => none
  | x :: xs => some (x, xs)
```

The most basic contract: **pushing then popping gives back what you pushed**.
"

abbrev Stack (α : Type) := List α

def Stack.push (x : α) (s : Stack α) : Stack α := x :: s

def Stack.pop : Stack α → Option (α × Stack α)
  | [] => none
  | x :: xs => some (x, xs)

/-- Pushing then popping returns the pushed element and original stack. -/
TheoremDoc push_pop_cancel as "push_pop_cancel"

Statement push_pop_cancel {α : Type} (x : α) (s : Stack α) :
    Stack.pop (Stack.push x s) = some (x, s) := by
  Hint "Unfold both definitions with `simp [Stack.push, Stack.pop]`."
  simp [Stack.push, Stack.pop]

Conclusion "
The proof is just one line — unfold the definitions and the equation holds.
That's the beauty of simple contracts: the spec is obvious, and the proof is automatic.

In a real system, you might swap the `List` implementation for an `Array` or a
ring buffer. The contract stays the same; only the proof changes.
"

/-- A stack: last-in, first-out. -/
DefinitionDoc Stack as "Stack"
/-- Push an element onto a stack. -/
DefinitionDoc Stack.push as "Stack.push"
/-- Pop the top element from a stack. -/
DefinitionDoc Stack.pop as "Stack.pop"
NewDefinition Stack Stack.push Stack.pop
