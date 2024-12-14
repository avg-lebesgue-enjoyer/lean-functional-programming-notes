/- @file Notes/Chapter4/Sec6Coe.lean
 - @src yeah I downloaded the website to PDF lol
 -/

/- IMPORTS: -/

import Notes.Chapter4.Sec1Pos



/- SECTION: Coersion `Pos → Nat` -/

/- Lean offers
` class Coe (α : Type) (β : Type) where `
`   coe : α → β                         `
which does coercion (*typecasting*) from things of type `α` to things of type `β`.
Whenever a thing of type `α` is found where a thing of some other type `γ` is expected,
 Lean searches the digraph of `Coe` instances to find a (perhaps *composite*) `Coe α γ`
 instance. If it finds one, it uses it.
This search is robust to infinite loops -- it's a (probably two-way) BFS, after all.
-/

instance : Coe Pos Nat where coe x := x.toNat

#eval [1, 2, 3].drop (2 : Pos) -- Here, a `Coe`rsion `Pos ⇝ Nat` is done.
def oneInt : Int := Pos.one    -- Here, a composite `Coe`rcion `Pos ⟶ Nat ⟶ Int` is done.

def oOO : Option (Option (Option String)) := "me" -- Composite `String ⟶ Option String ⟶ Option (Option String) ⟶ Option (Option (Option String))` is done.
#eval oOO

-- You can manually force `coe`rcions by inserting an `↑`:
def oOO' : Option (Option (Option String)) := ↑"me" -- forced `coe`rcion here :)



/- SECTION: Dependent coercions -/
-- yeah so that works like how you think it does.

structure NonEmptyList (α : Type) where
  cons::
  head : α
  tail : List α

instance : Coe (NonEmptyList α) (List α) where
  coe xs := xs.head :: xs.tail

/- Lean provides:
               this is the value being coerced.
                          vvvvvvv
` class CoeDep (α : Type) (a : α) (β : Type) where `
`   coe : β ` <-- this is the value we coerce `a` into
-/
--    we can pattern match on the thing being coerced to give
--                    dependent coercion!
--                         vvvvvvvvv
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }



/- SECTION: CoeSort -/

structure Monoid where
  Carrier : Type
  unit    : Carrier
  join    : Carrier → Carrier → Carrier
def natPlus  : Monoid := ⟨ Nat, 0, (· + ·) ⟩
def natTimes : Monoid := ⟨ Nat, 1, (· * ·) ⟩
def listCat (α : Type) : Monoid := ⟨ List α, [], (· ++ ·) ⟩

-- While this is literally correct...
def foldMap' (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec cat : (α → M.Carrier) → List α → M.Carrier
    | _, []        => M.unit
    | g, (a :: as) => M.join (f a) (cat g as)
  cat f xs
-- ...the typing looks disgusting af due to the `.Carrier`s everywhere.
-- Using the `CoeSort` typeclass lets you do the "refer to a monoid by its underlying
--  set" abuse of notation.

instance : CoeSort Monoid Type where
  coe M := M.Carrier

def foldMap (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec cat : (α → M) → List α → M
    | _, []        => M.unit
    | g, (a :: as) => M.join (f a) (cat g as)
  cat f xs
-- Happy typechecker :)

/- Another use of `CoeSort` behind the scenes is with `if`.
-- `if` expects as its first argument a `: Prop`, but programmers usually
--  use it with a `Bool` first argument. Behind the scenes, we have
` instance : CoeSort Bool Prop where  `
`   coe b := (b = true)               `
--  which does the coercion for us.
-/

-- The `Sort` in `CoeSort` refers to *`Type` or `Prop`*. Something something
--  theorem prover, no Russel paradox.



/- SECTION: CoeFun -/

/- Lean offers
` class CoeFun (α : Type) (makeFunctionType : outparam (α → Type)) where  `
`   coe : (x : α) → makeFunctionType x                                    `
which allows for overriding of the syntax `· ·` (e.g. `f x`).
-/

structure Adder where
  howMuch : Nat

instance : CoeFun Adder (fun _ => Nat → Nat) where
  coe adder := (· + adder.howMuch)

def add420 : Adder := ⟨ 420 ⟩
#eval add420 69
