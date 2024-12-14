/- @file Notes/Chapter5/Sec0Why.lean
 - @src https://lean-lang.org/functional_programming_in_lean/monads.html
 -/

/- SECTION: Checking for None -/

namespace Check4None

def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none    => none
  | some a  => next a

def firstOfList (as : List α) : Option α :=
  as[0]?
  -- Desugars to:
  -- `match as[0]? with   `
  -- `| none    => none   `
  -- `| some a  => some a `

def firstAndThirdOfList'' (as : List α) : Option (α × α) :=
  match as[0]? with
  | none => none | some a0 =>
  match as[2]? with
  | none => none | some a2 =>
    some (a0, a2)

def firstAndThirdOfList' (as : List α) : Option (α × α) :=
  andThen as[0]? fun a0 =>
  andThen as[2]? fun a2 =>
    some (a0, a2)

infixl:55 " ~~> " => andThen

def firstAndThirdOfList (as : List α) : Option (α × α) :=
  as[0]? ~~> fun a0 =>
  as[2]? ~~> fun a2 =>
    some (a0, a2)

def firstThirdFifthSeventhOfList (as : List α) : Option (α × α × α × α) :=
  as[0]? ~~> fun a0 =>
  as[2]? ~~> fun a2 =>
  as[4]? ~~> fun a4 =>
  as[6]? ~~> fun a6 =>
    some (a0, a2, a4, a6)

end Check4None



/- SECTION: Propagating exceptions -/

namespace PropagatingExceptions

inductive Except (ε : Type) (α : Type) where
  | error : ε → Except ε α
  | ok    : α → Except ε α
deriving BEq, Hashable, Repr

def get (as : List α) (i : Nat) : Except String α :=
  match as[i]? with
  | none    => Except.error s!"Index {i} is out of bounds for list of length {as.length}"
  | some a  => Except.ok a

#eval get ["haha"] 0
#eval get ["haha"] 69

def getFirstThird' (as : List α) : Except String (α × α) :=
  match get as 0 with
  | Except.error e => Except.error e
  | Except.ok a0 =>
  match get as 2 with
  | Except.error f => Except.error f
  | Except.ok a2 =>
  Except.ok (a0, a2)

instance : Coe ε (Except ε α) where coe e := Except.error e

def andThen (thing : Except ε α) (funny : α → Except ε β) : Except ε β :=
  match thing with
  | Except.error e  => e
  | Except.ok a     => funny a

infixl:55 " ~~>' " => andThen

def getFirstThird (as : List α) : Except String (α × α) :=
  get as 0 ~~>' fun a0 =>
  get as 2 ~~>' fun a2 =>
  Except.ok (a0, a2)

#eval getFirstThird ["haha", "ligma", "balls", "sus"]
#eval getFirstThird ["haha", "ligma"]

end PropagatingExceptions



/- SECTION: Logging -/

namespace Logging

-- A value with some logs
structure WithLog (logs : Type) (α : Type) where
  log   : List logs
  value : α
deriving Repr

def andThen (incoming : WithLog μ α) (next : α → WithLog μ β) : WithLog μ β :=
  let {log := incomingLog,            value :=                    incomingValue} := incoming
  let {log :=                nextLog, value := nextValue} := next incomingValue
  ;   {log := incomingLog ++ nextLog, value := nextValue}
def pure (a : α) : WithLog μ α :=
  {log := [], value := a}
def log (this : μ) : WithLog μ Unit :=
  {log := [this], value := ()}

infixl:55 " ~~>'' " => andThen

def isEven (i : Int) : Bool := (i % 2 == 0)
def sumEvens : List Int → WithLog String Int
  | [] => pure 0
  | i :: is =>
    (if isEven i then log s!"{i} is even" else pure ())   ~~>'' fun () =>
    (sumEvens is)                                         ~~>'' fun sum =>
    if isEven i then pure (i + sum) else pure sum
#eval sumEvens [0, 1, 2, 3, 4, 5]

end Logging



/- SECTION: State -/

namespace State

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
def pure (a : α) : State σ α := fun s => (s, a)
def andThen (sa : State σ α) (f : α → State σ β) : State σ β :=
  fun s =>
    let (s', a) := sa s
    ; f a s'
infixl:55 " ~~> " => andThen
-- State-specific structure
def get : State σ σ :=            -- Read the current state (by chucking it in the output field)
  fun s => (s, s)
def set (s : σ) : State σ Unit := -- Overwrite the current state (and discard the value)
  fun _ => (s, ())

-- Bintree numberer
open BinTree in
def number' (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
  | leaf => (n, leaf)
  | branch l a r =>
    let (n', l') := number' n l
    let a' := (n' + 1, a)
    let (n'', r') := number' (n' + 1) r
    ; (n'', branch l' a' r')
#eval number' 0 aTree

-- Cooler bintree numberer
open BinTree in
def number (as : BinTree α) : State Nat (BinTree (Nat × α)) :=
  match as with
  | leaf => pure leaf
  | branch l a r =>
    number l              ~~> fun numberedLeft  =>
    get                   ~~> fun n             =>
    set (n + 1)           ~~> fun ()            =>
    number r              ~~> fun numberedRight =>
    pure $ branch numberedLeft (n, a) numberedRight
#eval number aTree 0

-- open BinTree in
-- def BinTree.tagDepths : BinTree α → BinTree (Nat × α) :=
--   let rec helper (d : Nat) : BinTree α → BinTree (Nat × α)
--     | leaf          => leaf
--     | branch l a r  => branch (helper (d + 1) l) (d, a) (helper (d + 1) r)
--   ; helper 0
-- -- Tag each value with the string to print out there
-- def BinTree.tagWithWhitespace [ToString α] (as : BinTree α) : BinTree String :=
--   map (fun (d, a) => String.mk (List.replicate d ' ') ++ (toString a)) as.tagDepths
-- -- Convert a tree of strings to a long string to print out, broken by newlines
-- open BinTree in
-- def BinTree.toLongString : BinTree String → String
--   | leaf => ""
--   | branch l s r =>
--     let left := l.toLongString
--     let right := r.toLongString
--     ; left ++ "\n" ++ s ++ "\n" ++ right
-- -- The printer
-- def BinTree.toString [ToString α] (as : BinTree α) : String :=
--   as.tagWithWhitespace.toLongString

-- #eval aTree.tagDepths
-- #eval aTree.tagWithWhitespace

end State
