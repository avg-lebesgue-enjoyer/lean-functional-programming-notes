/- @file Notes/Chapter1/Section6.lean
 - @src https://lean-lang.org/functional_programming_in_lean/getting-to-know/polymorphism.html
 -/

namespace h -- avoid namespace conflicts with standard library. This is a hack.

/- SECTION: Polymorphism -/
-- As with `Haskell`, this refers to allowing arbitrary types. That is,
--  expressions of type `∀ (α : Type) . T α` are polymorphic in `α`.

structure Pair' (α : Type) where
  first'  : α
  second' : α
deriving Repr

def natOrigin' : Pair' Nat :=
  { first' := 0, second' := 0 : Pair' Nat }
#eval natOrigin'
#check (natOrigin')

def replaceFirst'' (α : Type) (p : Pair' α) (newFirst' : α) : Pair' α :=
  { p with first' := newFirst' }
#check replaceFirst'' Nat
#check (replaceFirst'')
#eval replaceFirst'' Nat natOrigin' 69

-- We can use *implicit arguments* to make this nicer:
def replaceFirst {α : Type} (p : Pair' α) (newFirst' : α) : Pair' α :=
  { p with first' := newFirst' }
-- Here, the typechecker is informed to try to infer the value `α : Type`.
-- So, for example,
#check replaceFirst natOrigin' 69
#eval replaceFirst natOrigin' 69
-- infers `α = Nat`.

inductive Sign where
  | positive : Sign
  | negative : Sign -- you can drop the `: Sign` here if you want; `Lean4` infers it.
deriving Repr

-- Dependent return types are possible, which is kinda cursed but also really cool:
def plusOrMinusThree
  (s : Sign)
  : match s with
    | Sign.positive => Nat
    | Sign.negative => Int
:=
  match s with
  | Sign.positive => (3  : Nat)
  | Sign.negative => (-3 : Int)
#check plusOrMinusThree Sign.positive



/- SECTION: List types -/

inductive List (α : Type) where
  | nil  : List α
  | cons : α → List α → List α
deriving Repr

def nil  {α : Type} : List α              := List.nil
def cons {α : Type} : α → List α → List α := List.cons

def primesUnder10 : List Nat :=
  cons 2 (cons 3 (cons 5 (cons 7 nil)))
#eval primesUnder10
#check [2, 3, 5, 7] -- Lean's standard library
#check []                   -- Lean's stdlib's `nil`
#check (λ x xs ↦ x :: xs)   -- Lean's stdlib's `cons`

#check List.length -- This exists



/- SECTION: Option -/

-- Lean's `Option : Type → Type` is Haskell's `Maybe :: * -> *`.
inductive Option (α : Type) : Type where
  | none              : Option α
  | some (value : α)  : Option α
deriving Repr
def none {α : Type} : Option α      := Option.none
def some {α : Type} : α → Option α  := Option.some

def List.head? {α : Type} (xs : List α) : Option α :=
  match xs with
  | List.nil      => none
  | List.cons x _ => some x
#eval (nil.head?          : Option Nat) -- forced type inference
#eval nil.head?              (α := Nat) -- forced type assignment
#eval (cons 1 nil).head?



/- SECTION: Product types -/

-- `× := Prod` is Haskell's `(,)`.

structure Prod' (α β : Type) : Type where
  fst : α
  snd : β
deriving Repr
-- Lean's stdlib calls this `Prod` and provides infix `×` (`\times`) for it
--    smth like `notation:65 α " × " β => Prod α β` is in lean's stdlib
-- It also exports `(⬝, ⬝)` which does what you think, and `(⬝, ⬝, ⬝) := (⬝, (⬝, ⬝))` etc.
-- Furthermore, `⬝ × ⬝ × ⬝ := ⬝ × (⬝ × ⬝)`



/- SECTION: Sum types -/

-- `⊕ := Sum` is Haskell's `Either`.

inductive Sum' (α β : Type) : Type where
  | inl : α → Sum' α β    -- `inl` short for "**in**jection on the **l**eft"
  | inr : β → Sum' α β    -- `inr` short for what you think it is
deriving Repr



/- SECTION: Unit type -/

-- This is the_≃ type with one element
inductive Unit' : Type where
  | unit : Unit'
deriving Repr
-- Lean's stdlib exports `Unit`, with type constructor `() := unit : Unit`.
-- For instance, `main : IO Unit` appears in `/Main.lean`,
--  and `IO.println` has return type `IO Unit`.



/- SECTION: Empty type -/

-- This is the_≃ type with no terms
inductive Empty' : Type where
-- yep, that's it.
#check Empty'
-- It's essentially typescript's `never`, which is useful for reasoning about
--  code that has special restrictions.


/- SECTION: EXERCISES -/

-- Write a function to find the last entry in a list. It should return an Option.
def last {α : Type} (xs : List α) : Option α :=
  match xs with
  | List.nil => none
  | List.cons lastElement List.nil => some lastElement
  | List.cons _ tail => last tail
#eval last List.nil  (α := Nat)
#eval last $ List.cons 1 List.nil
#eval last $ List.cons 1 (List.cons 2 List.nil)

-- Write a function that finds the first entry in a list that satisfies a given predicate.
def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | List.nil => none
  | List.cons x xs' =>
    if predicate x then some x else xs'.findFirst? predicate

-- Write a function Prod.swap that swaps the two fields in a pair.
def Prod.swap {α β : Type} (p : α × β) : β × α :=
  match p with
  | { fst := a, snd := b } => { fst := b, snd := a }

-- Rewrite the PetName example to use a custom datatype and compare it to the version that uses Sum.
def no : Empty := sorry

-- Write a function zip that combines two lists into a list of pairs.
-- The resulting list should be as long as the shortest input list.
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | List.nil => nil
  | List.cons x xs' =>
  match ys with
  | List.nil => nil
  | List.cons y ys' =>
  List.cons (x, y) $ zip xs' ys'

-- Write a polymorphic function `take` that returns the first `n` entries in a list,
--  where `n` is a `Nat`.
-- If the list contains fewer than n entries, then the resulting list should be the
--  input list.
def take {α : Type} (n : Nat) (xs : List α) : List α :=
  if n == 0 then nil else
  match xs with
  | List.nil        => nil
  | List.cons x xs' => List.cons x $ take (n - 1) xs'
#eval take 3 (cons 0 (cons 1 (cons 2 (cons 3 nil))))
#eval take 3 (cons 0 (cons 1 nil))
#eval take 0 (cons 0 nil)
#eval (take 69 nil     : List Nat)

-- Using the analogy between types and arithmetic, write a function that distributes
--  products over sums. In other words, it should have type
--  `α × (β ⊕ γ) → (α × β) ⊕ (α × γ)`.
def distribute {α β γ : Type} : α × (β ⊕ γ) → (α × β) ⊕ (α × γ) :=
  λ (a, e) ↦ -- you can pattern match at declaration time!
  match e with
  | _root_.Sum.inl b => _root_.Sum.inl (a, b)
  | _root_.Sum.inr c => _root_.Sum.inr (a, c)
-- The reverse function is possible by `colim lim --> lim colim`. Thus,
--    `α × (β ⊕ γ) ≃_{Type} (α × β) ⊕ (α × γ)`

-- Using the analogy between types and arithmetic, write a function that turns
--  multiplication by two into a sum. In other words, it should have type
--  `Bool × α → α ⊕ α`.
def double {α : Type} : Bool × α → α ⊕ α :=
  λ (b, a) ↦
  match b with
  | false => _root_.Sum.inl a
  | true  => _root_.Sum.inr a



-- End namespace `h`
end h
