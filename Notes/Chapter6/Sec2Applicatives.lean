/- @file Notes/Chapter6/Sec2Applicatives.lean
 - @src https://lean-lang.org/functional_programming_in_lean/functor-applicative-monad/applicative.html
 -/

/- SECTION: Applicative Functors -/

#print Applicative
#print Pure
#print Seq
-- This all unrolls to
class Applicative' (f : Type u → Type v) extends Functor f where
  pure : α → f α
  seq  : f (α → β) → (Unit → f α) → f β
-- Where `(Unit → f α)` is written in Lean, Haskell instead has just `f α`.
-- These two type signatures are isomorphic, on account of `⌈1 → α⌋ ≃ α`.
-- However, from a computational perspective, *this allows one to delay the **computation** of a side-effect* in that `f α`
--  argument.

-- Of course, the coherence laws carry from Haskell too.

instance : Applicative Option where
  pure x := .some x
  seq | .none,   _ => .none
      | .some f, x => f <$> (x ())  -- `(x ())` and `x ()` are both fine here

instance : Applicative (Except ε) where
  pure x := .ok x
  seq | .error e, _ => .error e
      | .ok f,    x => f <$> (x ())

-- The Book has this absolute gem of an explanation for why we care about applicatives here:
/-
Monads can be seen as a way of capturing the notion of sequentially executing statements into a pure functional language.
The result of one statement can affect which further statements run. This can be seen in the type of bind: m α → (α → m β) → m β.
The first statement's resulting value is an input into a function that computes the next statement to execute. Successive uses of
 bind are like a sequence of statements in an imperative programming language, and bind is powerful enough to implement control
 structures like conditionals and loops.

Following this analogy, Applicative captures function application in a language that has side effects.
The arguments to a function in languages like Kotlin or C# are evaluated from left to right.
Side effects performed by earlier arguments occur before those performed by later arguments.
A function is not powerful enough to implement custom short-circuiting operators that depend on the specific value of an argument,
 however.
-/

-- `(· <*> ·) : [Applicative m] → m (α → β) → m α → m β` is defined by putting the `fun () => ⋯` into the second argument of `seq`.
-- That is, `(mf <*> ma) := seq mf (fun () => ma)`
#check (· <*> ·)



/- SECTION: A non-monadic applicative (worked example) -/

-- Raw user input
structure RawInput where
  name      : String
  birthYear : String
deriving Repr
-- Logic to be validated
--  1. The `name` must not be the empty string
--  2. The `birthYear` must be numeric and non-negative
--  3. The `birthYear` must be > 1900, and ≤ (the current year)

-- A *subtype* is what it sounds like. It's restricted by satisfaction of a predicate `p`
structure Subtype' {α : Type} (p : α → Prop) where
  val : α             -- a thing `val : α`
  property : p val    -- a proof that `p val` is true
-- So, `Subtype α p  :=  (p = true \ α)`.
-- NOTE: `Subtype p` is what you write, not `Subtype α p`. `{α : Type}` is an *implicit* argument, after all
-- NOTE: `Subtype p` has special syntax: `{x : α // p x}` (or `{x // p x}` when `α` can be inferred).
def PositiveNat : Type := {x : Nat // x > 0}
example : PositiveNat := ⟨1, by simp⟩
instance {n : Nat} : OfNat PositiveNat (n + 1) where
  ofNat := ⟨n + 1, by simp_arith⟩
def Nat.asPositiveNat? (n : Nat) : Option PositiveNat :=
  if h : n > 0 then some ⟨n, h⟩ else none   -- NOTE: `h : n > 0` only gets bound in the `then ⋯` branch.

-- Structure representing fully validated input
structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // 1900 < y  ∧  y ≤ thisYear}
deriving Repr

-- This was fun
instance : Append { as : List α // ¬ as = [] } where
  append as bs :=
    let gamer : as.val = [] → ¬bs.val = [] :=
      fun wrong => nomatch (as.property wrong)  -- `nomatch` indicates contradiction :)
    let gamer2 : (as.val = [] → ¬bs.val = []) → ¬ (as.val ++ bs.val = []) := by simp  -- no idea what `simp` does here
    ⟨as ++ bs, gamer2 gamer⟩
#print absurd -- NOTE: This is a cool helper function

-- Inductive type for validating data
inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : {es : List ε // ¬ es = []} → Validate ε α
deriving Repr
-- which is a `Functor`
instance : Functor (Validate ε) where
  map f | .ok a     => .ok (f a)
        | .errors e => .errors e
-- and an `Applicative`, accumulating errors as we go
instance : Applicative (Validate ε) where
  pure := .ok
  seq
  | .ok f,      dva =>
    f <$> dva ()
  | .errors ef, dva =>
    match dva () with
    | .ok _ => .errors ef
    | .errors ea => .errors $ ef ++ ea

-- Okay, more programming
def Field := String
def reportError (field : Field) (message : String) : Validate (Field × String) α :=
  .errors ⟨[(field, message)], by simp⟩

def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if pf : name ≠ "" then .ok ⟨name, pf⟩ else reportError "Name" "Name must not be empty!"

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .ok a     => next a
  | .errors e => .errors e

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | none   => reportError "Year" "Year must be a natural number!"
  | some y => pure y

def checkBirthYear (currentYear yearToValidate : Nat) : Validate (Field × String) {y : Nat // 1900 < y ∧ y ≤ currentYear} :=
  if pf : 1900 < yearToValidate ∧ yearToValidate ≤ currentYear
  then .ok ⟨yearToValidate, pf⟩
  else reportError "Year" "Year must be in bounds!"

def checkInput (currentYear : Nat) (rawInput : RawInput) : Validate (Field × String) (CheckedInput currentYear) :=
  pure CheckedInput.mk
  <*> checkName (rawInput.name)
  <*> (Validate.andThen (checkYearIsNat rawInput.birthYear) (checkBirthYear currentYear))

#print RawInput
def example0 : RawInput where
  name      := ""
  birthYear := "moment"
def example1 : RawInput where
  name      := "amon"
  birthYear := "gus"
def example2 : RawInput where
  name      := ""
  birthYear := "1888"
def example3 : RawInput where
  name      := "sussus"
  birthYear := "1999"
#eval checkInput 2000 example0
#eval checkInput 2000 example1
#eval checkInput 2000 example2
#eval checkInput 2000 example3
