import Game.Levels.PurePrograms.L02_MyFilter

World "PurePrograms"
Level 3

Title "Folding a List"

Introduction "
`foldr` is the most general list combinator — it replaces `[]` with an initial value
and `::` with a binary function.

```lean
def myFoldr {α β : Type} (f : α → β → β) (init : β) : List α → β
  | []      => init
  | x :: xs => f x (myFoldr f init xs)
```

For example, `myFoldr (· + ·) 0 [1, 2, 3] = 1 + (2 + (3 + 0)) = 6`.

**Key insight**: if you fold with `(· :: ·)` and `[]`, you reconstruct the original list!

`myFoldr (· :: ·) [] [1, 2, 3] = 1 :: (2 :: (3 :: [])) = [1, 2, 3]`

**Your goal**: prove this identity law formally.
"

def myFoldr {α β : Type} (f : α → β → β) (init : β) : List α → β
  | []      => init
  | x :: xs => f x (myFoldr f init xs)

/-- `myFoldr (· :: ·) [] l = l` -/
TheoremDoc foldr_cons_nil as "foldr_cons_nil"

Statement foldr_cons_nil : ∀ {α : Type} (l : List α),
    myFoldr (· :: ·) [] l = l := by
  intro α l
  induction l with
  | nil          => simp [myFoldr]
  | cons x xs ih => simp [myFoldr, ih]

Conclusion "
`foldr (· :: ·) [] l = l` — folding cons and nil over a list reconstructs the list.
This is called the **foldr identity law**, and it shows that `myFoldr` is the
most general way to process a list.
"

/-- Fold a list from the right with a binary function and initial value. -/
DefinitionDoc myFoldr as "myFoldr"
NewDefinition myFoldr
