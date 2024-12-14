/- @file Notes/Chapter4/Sec2Poly.lean
 - @src https://lean-lang.org/functional_programming_in_lean/type-classes/polymorphism.html
 -/

/- SECTION: Type Classes and Polymorphism -/

#check @IO.println
-- `@IO.println : {α : Type u_1} → [inst : ToString α] → α → IO Unit`
-- The `[inst : ToString α]` here is an *implicit instance argument*.



/- SECTION: Defining Polymorphic Functions with Instance Implicits -/

-- You can omit the instance name `inst` in `[inst : Constraint]` when it isn't used.
-- (Really, invocation of a typeclass method desugars to a method that *finds* the
--  instance for you, and then accesses the instance's stuff)
def List.sum
    {α : Type}
    [Add α]       -- We need `α` to have a reasonable interpretation of `+`
    [OfNat α 0]   -- We need `α` to have a reasonable interpretation of `0`
    : List α → α  -- With this info, we can reduce a `List α` to an `α`
  | []      => 0
  | a :: as => a + as.sum

#check @List.sum
#eval ([1, 2, 3].sum : Int)

/- Behind the scenes:
    Given a
    ` class C α where `
    `   field0 : τ_0  `
    `   ...           `
    Lean generates a
    ` structure C α where `
    `   field0 : τ_0      `
    `   ...               `
    An `instance : C α` is a term of that product type, whose `field0` etc. are used
     when doing the typeclass stuff.
-/
/- When Lean goes to resolve one of `{these : These}`, it does this by doing automatic
    theorem proving stuff (*unification*) -- it tries to find a unique value of
    `these : These` that would make the program pass the typechecker.
   When Lean goes to resolve one of `[theseInstead : TheseInstead]`, it consults a
    lookup table instead.
   The result is that `{thisIs : ReallyFlexible}`, but somewhat expensive sometimes;
    meanwhile, `[theseAre : QuiteRigid]`, but incredibly cheap.
-/

structure Point (α : Type) where
  x : α
  y : α
deriving Repr

instance
  [Add α]         -- Knowing how to `Add α`,
  : Add (Point α) -- we know how to `Add (Point α)`
where
  add | ⟨a, b⟩, ⟨x, y⟩ => ⟨a + x, b + y⟩

#eval (⟨0, 1⟩ + ⟨4, 5⟩ : Point Nat)



/- SECTION: Exercise: Even Number Literals -/

structure Even where
  double::
  half : Nat

namespace Even

instance : ToString Even  where toString | double x      => (ToString.toString $ 2 * x) ++ " is even mate"
instance : Add Even       where add | double x, double y => double $ x + y
instance : Mul Even       where mul | double x, double y => double $ 2 * x * y

-- NOTE: This instance gives the `0` literal
instance : OfNat Even Nat.zero where
  ofNat := double 0
#eval (0 : Even)

-- NOTE: This instance is built recursively!
instance {n : Nat} [inst : OfNat Even n] : OfNat Even (n + 2) where
  -- Knowing that `n` is even (with proof `inst : OfNat Even n`),
  --  how do we prove that `n + 2` is even?
  -- Well, we take the proof that `n` is even, apply that proof, and access the
  --  halved value `inst.ofNat.half`. We `+ 1` to this, and double it. The result
  --  is a demonstration that `n + 2` is even.
  ofNat := double (inst.ofNat.half + 1)

end Even



/- SECTION: Exercise 2: Recursive Instance Search Depth -/

set_option diagnostics true
#eval (0 : Even)
#eval (2 : Even)
#eval (4 : Even)
#eval (8 : Even)
#eval (16 : Even)
#eval (32 : Even)
#eval (64 : Even)
#eval (128 : Even)
#eval (254 : Even)
-- NOTE: Lean fails to synthesise this instance.
--       It makes at most `128` recursive instance searches by default.
--       This is, of course, to prevent infinite loops in the interactive environment.
-- #eval (256 : Even)
set_option diagnostics false
