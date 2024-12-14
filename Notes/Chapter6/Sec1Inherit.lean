/- @file Notes/Chapter6/Sec1Inherit.lean
 - @src https://lean-lang.org/functional_programming_in_lean/functor-applicative-monad/inheritance.html
 -/

/- SECTION: Inheritance -/

-- Doing
structure MythicalCreature where
  large : Bool
deriving Repr
-- Generates
/-  `inductive MythicalCreature where         `
    ` | mk (large : Bool) : MythicalCreature  ` -/
#check MythicalCreature.mk
#check MythicalCreature.large

-- Inheritance is done like this:
structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr
-- which desugars to
/-  `inductive Monster where                                                          `
    ` | mk (toMythicalCreature : MythicalCreature) (vulnerability : String) : Monster ` -/
-- with `Monster.toMythicalCreature : Monster → MythicalCreature` the projection map.
#check Monster.mk
#check Monster.toMythicalCreature

-- In general,
/-  `structure Big extends Small where  `
    ` field : F                         ` -/
-- sets up `Big := Small × F` with projection maps
-- `Small ⟵ toSmall ── Big ── field ⟶ F`

-- As a convenience, `MythicalCreature.large : MythicalCreature → Bool` can be used as `Monster.large : Monster → Bool`.
#check MythicalCreature.large
def myMonster : Monster := { large := false, vulnerability := "sugoma" } -- using `large` instead of `toMythicalCreature` is a convenience too
#eval myMonster.large -- this shouldn't typecheck, but the obvious coersion `Monter → MythicalCreature` is applied.

-- Similarly,
def MythicalCreature.small (it : MythicalCreature) : Bool := ! it.large
-- allows
#eval myMonster.small



/- SECTION: Multiple inheritance -/

-- (for demo)
structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr

-- Multiple inheritance
structure MonstrousHelper extends Monster, Helper where
  -- (no further fields)
deriving Repr
-- This does exactly what you think it does, but with the subtlety that the *first* thing is
--  used as the base *((to resolve the "diamond problem":))*
--  ` MonstrousHelper --> Monster       `
--  `    |                   |          `
--  `    v                   v          `
--  ` Monster ------> MythicalCreature  ` *which path `MonstrousHelper --> MythicalCreature` should we take?*
#check MonstrousHelper.mk
#print MonstrousHelper.mk
#print MonstrousHelper.toHelper



/- SECTION: Default Field Declarations -/
-- This is what you think it is.

-- (for demo)
inductive Size where
  | small | medium  | large
deriving Repr, BEq

structure SizedCreature extends MythicalCreature where
  size  : Size
  large := size == Size.large -- Type information `large : Bool` is inferred, and in fact *must be omitted* for the syntax to understand this as a default field value
deriving Repr

def gamer : SizedCreature := { size := Size.small } -- `large := false` is computed and inferred.
#eval gamer
#eval gamer.large

def nonsense : SizedCreature := { size := Size.small, large := true } -- `large := true` is overwritten straight into the thing
#eval nonsense
#eval nonsense.large



/- SECTION: Type class inheritance -/

-- Since types are first-class in Lean, it shouldn't be surprising that type classes are
--  implemented by structures, resulting in a `: Type u` somewhere.
-- So... type classes have all the inheritance stuff we just discussed available too!
