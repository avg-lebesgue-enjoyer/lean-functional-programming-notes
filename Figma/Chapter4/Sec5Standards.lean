/- @file Notes/Chapter4/Sec5Standards.lean
 - @src https://lean-lang.org/functional_programming_in_lean/type-classes/standard-classes.html
 -/

/- IMPORTS: -/

import Notes.Chapter4.Sec1Pos



/- SECTION: Arithmetic -/

/-
` Expression | Desugars to    `
`------------+----------------`
` x + y      | HAdd.hAdd x y  `
` x - y      | HSub.hSub x y  `
` x * y      | HMul.hMul x y  `
` x / y      | HDiv.hDiv x y  `
` x % y      | HMod.hMod x y  `
` x ^ y      | HPow.hPow x y  `
` (- x)      | Neg.neg   x    `
The namespace here is also the `class` name.
There also exist bitwise operators but I'm not gonna bother.
-/



/- SECTION: Equality -/

-- Lean has two types of equality:
--  **Propositional equality** is the mathematical statement that two things are
--    equal, such as in the type `1 = 2` (which is empty). This is for use as a
--    theorem prover. Notated using `=`.
--  **Boolean equality** is the programming runtime check, returning of type `Bool`.
--    This is more for use as a programming language. Notated using `==`.
-- Boolean equality `==` is provided by `BEq.beq`.

def Pos.beq : Pos → Pos → Bool
  | Pos.one, Pos.one => true
  | Pos.succ x, Pos.succ y => x.beq y
  | _, _ => false
instance : BEq Pos where beq := Pos.beq

#eval (3 : Pos) == (4 : Pos)
#eval (3 : Pos) == (3 : Pos)

-- NOTE: `<` calls `LT.lt : [LT α] → α → α → Prop` under the hood.
--  This returns a `Prop`osition, not a `Bool`ean. Lean does the coersion for us,
--  letting us use `<` in programs with just as much convenience as `==`.
#check LT.lt
#check 2 < 4
#eval if 2 < 4 then "yeppo" else "nah mate"

/- The comparisons are done like this under the hood:
` Expression  | Desugars to   `
`-------------+---------------`
` x < y       | LT.lt x y     `
` x ≤ y       | LE.le x y     `
` x > y       | LT.lt y x     `
` x ≥ y       | LE.le y x     `
and the class name is the namespace above
-/

-- The `Ordering` type
inductive Ordering' where | lt | eq | gt
-- The `Ord` typeclass:
class Ord' (α : Type) where
  compare : α → α → Ordering

instance : Ord Pos where
  compare :=
  let rec theCompare
    | Pos.one,    Pos.one     => Ordering.eq
    | Pos.one,    Pos.succ _  => Ordering.lt
    | Pos.succ _, Pos.one     => Ordering.gt
    | Pos.succ x, Pos.succ y  => theCompare x y
  ; theCompare
#eval let funny | Ordering.lt => "lt" | Ordering.eq => "eq" | Ordering.gt => "gt"
      ; funny $ Ord.compare (2 : Pos) (3 : Pos)



/- SECTION: Hashing -/

class Hashable' (α : Type) where
  hash : α → UInt64
-- with the contract that Java uses:
--  if `Ord α`, then `∀ a b : α, a == b ⟶ hash x == hash y`

-- The standard library provides `mixHash` for combining hashes:
#check @mixHash
def Pos.hash : Pos → UInt64
  | Pos.one     => 0
  | Pos.succ x  => mixHash 1 x.hash
instance : Hashable Pos where hash := Pos.hash

inductive BinTree (α : Type) where
  | leaf    : BinTree α
  | branch  : BinTree α → α → BinTree α → BinTree α

namespace BinTree
def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | .leaf, .leaf => true
  | .branch l a r, .branch l' a' r' =>
    l.eqBinTree l' && a == a' && r.eqBinTree r'
  | _, _ => false
end BinTree
instance [BEq α] : BEq (BinTree α) where beq := BinTree.eqBinTree

/- NOTE: You can `deriving` many of the standard typeclasses, because the
          code to generate them is catamorphic.
         Fwiw, you can derive them later too, not just when you defin the type:
` deriving instance BEq for Pos `
-/



/- SECTION: Appending -/

/-
` class HAppend (α : Type) (β : Type) (γ : outparam Type) where `
`   hAppend : α → β → γ                                         `
` syntax a " ++ " b => HAppend.hAppend a b                      `
There's a homogeneous version `Append.append` too :)
-/

structure NonEmptyList (α : Type) where
  cons::
  head : α
  tail : List α
deriving Repr, BEq, Hashable

instance : Append (NonEmptyList α) where
  append
  | { head := x, tail := xs }, { head := y, tail := ys } =>
    { head := x, tail := xs ++ (y :: ys) }

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend
  | { head := x, tail := xs }, ys =>
    { head := x, tail := xs ++ ys }



/- SECTION: FUNCTORS YAY MY FAV <3 :)))))))) :DDDD ! -/

#eval (· + 1) <$> [1, 2, 3]

instance : Functor NonEmptyList where
  -- `map : (α → β) → NonEmptyList α → NonEmptyList β`
  map | f, { head := x, tail := xs } => { head := f x, tail := f <$> xs }

-- This exists too, by the law `mapConst x = map (fun _ => x)`.
-- This law is actually a default definition of it, which the programmer can
--  override if they have something more efficient to use instead.
#check Functor.mapConst

-- The full class looks like this:
class Functor' (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β
  mapConst {α β : Type} (b : β) (fa : f α) : f β
    := map (fun _ => b) fa -- this line ascribes the default definition

/- The functor laws are what you know them to be:
-- # Math: F 1_x = 1_{F x}
-- # Math: F (f ∘ g) = F f ∘ F g
-/

-- Unfortunately, you cannot `deriving Functor`

def BinTree.map {α β : Type} (f : α → β) : BinTree α → BinTree β
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l a r => BinTree.branch (BinTree.map f l) (f a) (BinTree.map f r)

instance : Functor BinTree where map := BinTree.map
