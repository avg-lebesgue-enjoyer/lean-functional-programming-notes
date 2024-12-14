/- @file Notes/Chapter1/Section3.lean
 - @src https://lean-lang.org/functional_programming_in_lean/getting-to-know/functions-and-definitions.html
 -/

/- SECTION: Function and Definitions -/

def hello := "Hello"        -- infers     `hello : String`
def hi : String := "Hi!"    -- explicitly `hi : String`
#eval String.append hello hi
-- NOTE: Defined names are only in scope AFTER their definitions!
-- #eval shitpost   -- error: `unknown identifier 'shitpost'`
def shitpost : String := "shitpost"



/- SECTION: Defining Functions -/

def add1 (n : Nat) : Nat := n + 1
-- spacing is quite loose:
def add2 (n : Nat)    : Nat                :=
  n   + 1
#eval add1 1

-- Multiple argument syntax (really curried...)
def max' (a : Nat) (b : Nat) : Nat :=
  if a > b
  then a
  else b
#eval max' 1 2
#check max'   -- when an identifier is given to `#check`, the *signature* is shown.
#check (max') -- doing this forces the *type* to be shown

-- Shorter multi-argument syntax
def max'' (a b : Nat) : Nat := if a > b then a else b
#eval max'' 2 3
#check max''
#check (max'')

-- Function type. `\ to` with no space resolves to `→`.
-- Writing `->` is fine too.
def max''' : Nat → Nat → Nat
  := max'
#eval max''' 3 4
#check max'''
#check (max''')

/- SECTION: Exercises (Defining Functions) -/

def joinStringsWith (separator left right : String) : String :=
  String.append left (String.append separator right)

#check joinStringsWith "hello!"

def volume (length width depth : Nat) : Nat :=
  length * width * depth

#check (volume)



/- SECTION: Defining Types -/
-- NOTE: **TYPES ARE EXPRESSIONS IN LEAN**. They are first-class.
-- So what is their type? It's `Type`.
#check String
#check Nat
#check Type   -- ...and `Type   : Type 1`...
#check Type 1 -- ...and `Type 1 : Type 2`...

def Str : Type := String
#check Str
#check (Str)
def shitpost' : Str := "shitpost"
#check shitpost'
#check (shitpost')

def Nat' := Nat -- inferred `Nat' : Type`
-- def sixtyNine : Nat' := 69 -- This fails due to polymorphic number literals
def sixtyNine : Nat' := (69 : Nat) -- this goes through because `Nat = Nat'`.
abbrev N : Type := Nat -- Marks this definition as `unfoldable`, which means that the typechecker can go ahead and replace `N` with `Nat`.
def sixtyNine' : N := 69
#check sixtyNine'
