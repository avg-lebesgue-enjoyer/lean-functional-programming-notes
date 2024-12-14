/- @file Notes/Chapter4/Sec3InstSearch.lean
 - @src https://lean-lang.org/functional_programming_in_lean/type-classes/out-params.html
 -/

/- SECTION: Imports -/

import Notes.Chapter4.Sec1Pos
#check Pos -- :)

/- SECTION: Controlling Instance Search -/

def addNatPos : Nat → Pos → Pos
  | 0,     x  => x
  | n + 1, x  => Pos.succ $ addNatPos n x

def addPosNat : Pos → Nat → Pos :=
  let swap f x y := f y x
  ; swap addNatPos

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos
instance : HAdd Pos Nat Pos where
  hAdd := addPosNat
#eval toString ((1 : Nat) + (5 : Pos) : Pos)
#eval toString ((1 : Pos) + (5 : Pos) : Pos)
-- We shouldn't expect the typechecker to figure out the output type here:
#eval (1 : Nat) + (5 : Pos)
-- but it does. The reason is due to `outParam`s, which we'll explore in a sec

class HAdd' (α : Type) (β : Type) (γ : Type) where
  hAdd' : α → β → γ
instance : HAdd' Nat Pos Pos where hAdd' := addNatPos
instance : HAdd' Pos Nat Pos where hAdd' := addPosNat
#eval (HAdd'.hAdd' (1 : Nat) (5 : Pos) : Pos) -- We need to explicitly designate the return type `: Pos` here.



/- SECTION: Output Parameters -/

class HAdd'' (α : Type) (β : Type) (γ : outParam Type) where
  hAdd'' : α → β → γ
instance : HAdd'' Nat Pos Pos where hAdd'' := addNatPos
instance : HAdd'' Pos Nat Pos where hAdd'' := addPosNat
#eval HAdd''.hAdd'' (1 : Nat) (5 : Pos) -- No outparam designation necessary; Lean now tries to fill it in when it does the instance search for us :)



/- SECTION: Default instances -/

-- This is a default instance, and it tells the instance finder to assume that this one
--  is safe to use if it ever gets stuck.
-- **DEFUALT INSTANCES SHOULD BE USED RARELY AND CAREFULLY**, since they fuck with what
--  would otherwise be a more general return type.
@[default_instance]
instance [inst : Add α] : HAdd' α α α where hAdd' := inst.add -- Thanks to inferring instances when necessary, `inst.add` could be replaced by `Add.add` and Lean will find `inst` and use it.

#check HAdd'.hAdd' 5 -- This now has type `Nat → Nat`, rather than `β → γ`.



/- EXERCISE: Scalar multiplication -/

structure Point (α : Type) where
  x : α
  y : α
deriving Repr

-- Addition
instance [Add α] : Add (Point α) where
  add | ⟨a, b⟩, ⟨x, y⟩ => ⟨ a + x, b + y ⟩

-- Scalar multiplication
instance [Mul α] : HMul α (Point α) (Point α) where
  hMul | s, ⟨x, y⟩ => ⟨ s * x, s * y ⟩

-- We now have 2D vector structure:
#eval 2 * (⟨1, 4⟩ : Point Nat) + ⟨5, 6⟩
-- Using dependent types, we'll see how to make arbitrary finite dimensions later :)
