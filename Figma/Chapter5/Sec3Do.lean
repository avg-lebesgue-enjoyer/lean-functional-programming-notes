/- @file Notes/Chapter5/Sec3Do.lean
 - @src https://lean-lang.org/functional_programming_in_lean/monads/do.html
 -/

/- IMPORTS: Bintree -/

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving BEq, Repr

open BinTree in
def BinTree.map (f : α → β) : BinTree α → BinTree β
  | leaf          => leaf
  | branch l a r  => branch (map f l) (f a) (map f r)
instance : Functor BinTree where map := BinTree.map

open BinTree in
def aTree :=
  branch
    (branch
       (branch leaf "a" (branch leaf "b" leaf))
       "c"
       leaf)
    "d"
    (branch leaf "e" leaf)
#eval aTree

-- We want to make a function that eats a `BinTree α` and produces a `BinTree (Nat × α)` by
--  labelling each branch with its in-order traversal number.
-- Traditionally, you'd do this by walking around with a global variable... ouch.
-- We get around this with the state monad

def State (σ : Type) (α : Type) : Type :=
  σ → σ × α
#check State Int Int

instance (σ : Type) : Functor (State σ) where
  map {α β : Type} (f : α → β) (sa : State σ α) (currentState : σ) :=
    let (s, a) := sa currentState
    ;   (s, f a)

-- Monadic structure
def State.pure (a : α) : State σ α := fun s => (s, a)
def State.andThen (sa : State σ α) (f : α → State σ β) : State σ β :=
  fun s =>
    let (s', a) := sa s
    ; f a s'
instance : Monad (State σ) where
  pure := State.pure
  bind := State.andThen
-- State-specific structure
def get : State σ σ :=            -- Read the current state (by chucking it in the output field)
  fun s => (s, s)
def set (s : σ) : State σ Unit := -- Overwrite the current state (and discard the value)
  fun _ => (s, ())



/- SECTION: Amon Gus -/

-- Helper method that returns the current state, and then increments it for
-- the next use. i.e. it's a use of "state++".
def increment : State Nat Nat := do
  let x ← get
  set $ x + 1
  pure x

-- Coolest bintree numberer
open BinTree in
def numberCoolest (as : BinTree α) : State Nat (BinTree (Nat × α)) :=
  match as with
  | leaf => pure leaf
  | branch l a r => do
    pure $ branch (← numberCoolest l) ((← increment), a) (← numberCoolest r)
#eval numberCoolest aTree 0
