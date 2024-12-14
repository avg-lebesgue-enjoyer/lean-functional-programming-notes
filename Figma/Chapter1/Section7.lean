/- @file Notes/Chapter1/Section7.lean
 - @src https://lean-lang.org/functional_programming_in_lean/getting-to-know/conveniences.html
 -/

-- namespace h -- hack avoiding name conflicts

/- SECTION: Automatic implicit arguments -/
-- Just like `length :: [a] -> Integer` in Haskell automatically completes to
--  `length :: forall a. [a] -> Integer`, Lean automatically makes implicit
--  arguments out of dangling names. For instance,
def length : List α → Nat :=
  fun xs =>
  match xs with
  | []        => 0
  | _ :: xs'  => length xs' + 1
#check (length) -- type info equivalent to `length : {α : Type} : List α → Nat`

/- SECTION: Pattern matching definitions -/

-- simple pattern matching of one argument without `match`
def length' : List α → Nat
  | [] => 0
  | _ :: xs' => length xs' + 1

-- multi-argument pattern matching
def drop : Nat → List α → List α
  | 0, xs               => xs
  | _, []               => []
  | Nat.succ n, _ :: xs => drop n xs

-- You can even do this in a mix with named arguments!
def fromOption (default : α) : Option α → α
  | none    => default
  | some x  => x
-- NOTE: In the stdlib, this is called `Option.getD : {α : Type} → α → Option α → α`.



/- SECTION: Local definitions -/

-- Because Lean *strictly* evaluates, this is exponential time:
def unzip' : List (α × β) → (List α) × (List β)
  | []              => ([], [])
  | (x, y) :: xys'  => (x :: (unzip' xys').fst, y :: (unzip' xys').snd)

-- You can force it to pre-compute by using a `let` expression:
def unzip : List (α × β) → (List α) × (List β)
  | [] =>
    ([], [])
  | (x, y) :: xys' =>
    let (xs, ys) := unzip xys'  -- If there's only one possible pattern, you can destructure immediately
    ; (x :: xs, y :: ys)        -- `;` is the `in` from Haskell, except not really; it's not necessary unless you write it on the same line as the `let`.

-- Recursive definitions in a `let` must be declared with `let rec`.
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar         => soFar
    | (a :: as), soFar  => helper as (a :: soFar)
  ; helper xs []
-- This is efficient because Lean is strict (whereas Haskell is lazy)



/- SECTION: Type inference -/
-- Lean will do it, but it needs help sometimes.
-- If in doubt, provide the type explicitly.

-- e.g.
def unzip'' (xys : List (α × β)) := -- return type inferred to be `List α × List β`
  match xys with
  | [] => ([], [])
  | (x, y) :: xys' =>
    let (xs, ys) := unzip'' xys'
    ; (x :: xs, y :: ys)
#check (unzip'')



/- SECTION: Natural number patterns -/

-- `n + k` matches the pattern `Nat.succ (... (Nat.succ n)...)` with `k` `Nat.succ`s.
-- NOTE: for obvious reasons, the second argument `k` MUST BE COMPILE-TIME CONSTANT.
def even : Nat → Bool
  | 0     => true
  | 1     => false
  | n + 2 => even n



/- SECTION: Anonymous functions -/

-- keywords `fun` `λ` `=>` `↦`
def funny   : Nat → Nat := fun x => x
def funny'  : Nat → Nat := λ   x ↦ x     -- `↦` has awful 1.5-character spacing, fuck that
def funny'' : Nat → Nat := fun (x : Nat) => (x : Nat)

-- Support implicit arguments
#check fun {α : Type} (x : α) => x

-- Support pattern matching
#check fun
  | 0     => 0
  | n + 1 => n

-- Use `⬝` (`\cdot`) for some very simple anonymous functions!
-- This binds to the closest set of parentheses
-- #check (⬝ + 1) -- NOTE: My version of Lean really hates this and idk why



/- SECTION: Namespaces -/

-- Open namespace
namespace String
-- Stuff defined in here has the `String` namespace
def fart (_ : String) := "fart"
#check "poop".fart
#eval  "poop".fart
-- Close namespace
end String

-- You can re-open a namespace later for a single expression or command, meaning you don't need to
--  give its prefix over and over.
open String in
#check fart
-- same in expressions:
def outerFart : String :=
  open String in
  "poop".fart

/- You can open it for the rest of the file with
`open String`
-/



/- SECTION: if let -/

-- So this exists, and it's a conditional pattern match with a default
--  expression to compute on a failure to match:
def bigFart (ox : Option α) : String :=
  if let some _ := ox then "big fart" else "small fart"
#eval bigFart (none : Option Nat)
#eval bigFart (some 1)



/- SECTION: Positional structure arguments -/

structure Point where
  x : Float
  y : Float
deriving Repr

-- my IDE **hates** the \langle ... \rangle notation.



/- SECTION: String interpolation -/

-- `s!"some string {someVariable}"` is Lean's notation for template literals.
-- `someVariable : T` must have the instance `ToString T`.
-- It unrolls to string concatenation with a `toString` in the middle.

def hello       : String := "world"
def helloWorld  : String := s!"hello {hello}"
#eval helloWorld
