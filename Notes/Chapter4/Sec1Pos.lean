/- @file Notes/Chapter4/Sec1Pos.lean
 - @src https://lean-lang.org/functional_programming_in_lean/type-classes/pos.html
 -/

/- SECTION: Goals -/
-- We're gonna build some positive numbers, with overloaded arithmetic



/- SECTION: Positive Numbers -/

inductive Pos : Type where
  | one   : Pos
  | succ  : Pos → Pos
deriving Repr

/- Can't do this yet because no instance `OfNat Pos 7`:
    `def seven : Pos := 7`
-/



/- SECTION: Classes and instances -/

-- Let's add a `Plus` instance.
class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

#eval Plus.plus (3 : Nat) 4
#check Plus.plus (3 : Nat) 4

def Pos.plus : Pos → Pos → Pos
  | Pos.one,    y => Pos.succ y
  | Pos.succ x, y => Pos.succ $ Pos.plus x y

instance : Plus Pos where
  plus := Pos.plus

open Plus (plus) in
#eval plus Pos.one Pos.one

/- The "real" `Plus` in Lean is `HAdd`, short for `H`eterogeneous `Add`ition.
` class HAdd                      `
`       (α : Type u) (β : Type v) `
`       (γ : outParam (Type w))   `
`       : Type (max (max u v) w)  `
` where                           `
`   hAdd : α → β → γ              `
-/
/- There's a watered-down `Add`:
` class Add               `
`   (α : Type u)          `
`   : Type u              `
` where                   `
`   add : α → α → α       `
-- which is more like what we did.
-/

instance : Add Pos where
  -- `add : Pos → Pos → Pos`
  add := Pos.plus

open Pos in
def seven : Pos := succ $ succ $ succ $ succ $ succ $ succ $ one
def fourteen : Pos := seven + seven
#eval fourteen



/- SECTION: `ToString` -/

-- Another good one is `ToString`:
/-
` class ToString (α : Type u) : Type u where  `
`   toString : α → String                     `
-/

-- obvious catamorphism instance
def Pos.toNat : Pos → Nat
  | Pos.one     => 1
  | Pos.succ x  => Nat.succ x.toNat

instance : ToString Pos where
  -- `toString : Pos → String`
  toString x := toString x.toNat
#eval toString seven



/- SECTION: Multiplication -/

def Pos.mul : Pos → Pos → Pos
  | Pos.one,    y => y
  | Pos.succ x, y => y + Pos.mul x y

instance : Mul Pos where
  -- `mul : Pos → Pos → Pos`
  mul := Pos.mul



/- SECTION: Numeric literals -/

#check OfNat
/- We wanna implement `OfNat : Type → Nat → Type`:
` class OfNat (α : Type) (_ : Nat) where  ` <-- unnamed argument `: Nat` is the literal encountered
`   ofNat : α                             ` <-- this is the value to present
 -/

inductive Four : Type where
  | zero  : Four
  | one   : Four
  | two   : Four
  | three : Four
deriving Repr

namespace Four
instance : OfNat Four 0 where ofNat := zero
instance : OfNat Four 1 where ofNat := one
instance : OfNat Four 2 where ofNat := two
instance : OfNat Four 3 where ofNat := three
end Four

#eval (0 : Four)
#eval (1 : Four)
#eval (2 : Four)
#eval (3 : Four)

-- Epic use of implicit argument not of type `Type` :D
instance {n : Nat} : OfNat Pos (n + 1) where  -- NOTE: Lean is smart enough to infer the `{n : Nat}` automatically; it doesn't need to be listed here
  ofNat :=
    let rec returnMe : Nat → Pos
      | Nat.zero => Pos.one
      | Nat.succ n' => Pos.succ $ returnMe n'
    ; returnMe n

def eight : Pos := 8
#eval eight



/- SECTION: Exercise 1: Another Representation -/

structure Pos' where
  succ ::
  pred : Nat
deriving Repr

namespace Pos'

def add : Pos' → Pos' → Pos'
  | Pos'.succ x, Pos'.succ y => Pos'.succ $ x + y + 1

instance : Add Pos' where
  add := Pos'.add

def toString : Pos' → String
  | Pos'.succ x => ToString.toString (x + 1)

instance : ToString Pos' where
  toString := Pos'.toString

instance
  {n : Nat}
  : OfNat Pos' (n + 1)
where
  ofNat := Pos'.succ n

def mul : Pos' → Pos' → Pos'
  | Pos'.succ x, Pos'.succ y =>
    Pos'.succ $ x * y + x + y

instance : Mul Pos' where
  mul := Pos'.mul

end Pos'

#eval (2 + 3 * 5 : Pos').toString



/- SECTION: Exercise 2: Even numbers -/

structure Even where
  double::
  half : Nat

namespace Even

def toString : Even → String
  | double x => ToString.toString $ 2 * x

instance : ToString Even where
  toString := Even.toString

-- Lean struggles to apply this instance...
-- instance {n : Nat} : OfNat Even (n + n) where
  -- ofNat := double n

instance : Add Even where
  add | double x, double y => double $ x + y

instance : Mul Even where
  mul | double x, double y => double $ 2 * x * y

set_option linter.unusedVariables false
def ofNat (n : Nat) {x : Nat} {ok : n = 2 * x} : Even := double x
set_option linter.unusedVariables true
#check @ofNat

-- it doesn't like this instance either
instance {n : Nat} {x : Nat} {ok : n = 2 * x}
  : OfNat Even n
where
  ofNat := Even.ofNat n (x := x) (ok := ok)

end Even
