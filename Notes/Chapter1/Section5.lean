/- @file Notes/Chapter1/Section5.lean
 - @src https://lean-lang.org/functional_programming_in_lean/getting-to-know/datatypes-and-patterns.html
 -/

/- SECTION: Inductive data types -/

-- Sum type
inductive Bool' where
  | false' : Bool'
  | true'  : Bool'
deriving Repr
/- Exported namespace functions:
    `Bool'.false' : Bool'`
    `Bool'.true'  : Bool'`
  The standard library's `Bool : Type` re-exports
    `true := Bool.true` and `false := Bool.false`
  for convenience.
-/
def false' := Bool'.false'
def true' := Bool'.true'

-- Full-blown recursion
inductive Nat' where
  | zero' : Nat'
  | succ' : Nat' → Nat'   -- could alternatively have written `succ' (n : Nat') : Nat'`
deriving Repr
/- Exported namespace functions:
    `Nat'.zero' : Nat'`
    `Nat'.succ' : Nat' → Nat'`
-/
def zero' : Nat' := Nat'.zero'
def succ' : Nat' → Nat' := Nat'.succ'
#eval Nat'.zero'
#eval zero'



/- SECTION: Pattern matching -/

def isZero' (n : Nat') : Bool' :=
  match n with
  | Nat'.zero' => true'
  | Nat'.succ' _ => false'

#eval isZero' zero'
#eval isZero' $ succ' zero'

def pred' (n : Nat') : Nat' :=
  match n with
  | Nat'.zero'   => zero'
  | Nat'.succ' p => p

#eval pred' Nat'.zero'
#eval pred' $ succ' zero'
#eval pred' $ succ' (succ' zero')

structure Point where
  x : Float
  y : Float
deriving Repr

def magnitude (p : Point) : Float :=
  match p with
  | { x := x, y := y } =>
    (x^2 + y^2).sqrt

#eval magnitude { x := 0, y := 0 : Point }
#eval magnitude { x := 1, y := 1 : Point }



/- SECTION: Recursive functions -/

def not' (b : Bool') : Bool' :=
  match b with
  | Bool'.false' => true'
  | Bool'.true'  => false'

def isEven' (n : Nat') : Bool' :=
  match n with
  | Nat'.zero' => true'
  | Nat'.succ' x => not' (isEven' x)

#eval isEven' zero'
#eval isEven' $ succ' zero'
#eval isEven' $ succ' (succ' zero')

-- Termination checker uses *structural induction* rule to determine
--  termination here. This doesn't always work, but it often does.
def Nat'.plus' (x y : Nat') : Nat' :=
  match x with
  | Nat'.zero' => y
  | Nat'.succ' x' => Nat'.succ' $ x'.plus' y

def Nat'.times' (x y : Nat') : Nat' :=
  match x with
  | Nat'.zero' => zero'
  | Nat'.succ' x' => y.plus' $ x'.times' y

def Nat'.minus' (x y : Nat') : Nat' :=
  match y with
  | Nat'.zero'    => x
  | Nat'.succ' y' =>
    pred' $ x.minus' y'

-- The termination checker fails to successfully determine termination
--  using structural induction here:
def funnyDivide (x y : Nat) (p : y > 0) : Nat :=
  if x < y then 0 else
  Nat.succ $ funnyDivide (x - y) y p
  termination_by x -- actually, `Lean4` can infer this one **IF** we give it the proof `p : y > 0`.
