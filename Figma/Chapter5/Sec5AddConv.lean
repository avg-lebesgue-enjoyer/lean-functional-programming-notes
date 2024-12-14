/- @file Notes/Chapter5/Sec5AddConv.lean
 - @src https://lean-lang.org/functional_programming_in_lean/monads/conveniences.html
 -/

/- SECTION: Omitting namespaces with dots -/

inductive BinTree (α : Type) : Type where
  | leaf    : BinTree α
  | branch  : BinTree α → α → BinTree α → BinTree α
deriving Repr

def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf                                    -- `.leaf`  ~~> `BinTree.leaf`
  | .branch l a r => .branch (mirror r) a (mirror l)  -- `mirror` ~~> `BinTree.mirror`



/- SECTION: "or"-patterns -/

inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
  deriving Repr

def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true         -- `| .saturday | .sunday => true` desugars to `| .saturday => true ; | .sunday => true`
  | _ => false

def condense : α ⊕ α → α
  | .inl x | .inr x => x    -- Desugars to `| .inl x => x ; | .inr x => x`. This is a SYNTACTIC replacement, not compiled. So...

def shitpost : Nat ⊕ Weekday → String
  | .inl x | .inr x => s!"Amon Gus {repr x}"  -- the `x` here has type `Nat` on the `.inl x` branch, and type `Weekday` on the `.inr x` branch.
                                              -- The hover information in VSCode incorrectly reports that `x` *definitely* has type `Nat`.
