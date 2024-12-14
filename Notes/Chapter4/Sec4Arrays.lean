/- @file Notes/Chapter4/Sec4Arrays.lean
 - @src https://lean-lang.org/functional_programming_in_lean/type-classes/indexing.html
 -/

/- IMPORTS: -/

import Notes.Chapter4.Sec1Pos
import Notes.Chapter4.Sec3InstSearch



/- SECTION: Arrays -/

-- A Lean array is a Dynamic Array (Java's `ArrayList`), and is declared by
def cats : Array String := #["black", "calico", "white", "cute"]
#eval cats[0]
#eval cats[3]
#eval cats.size

-- Let's learn about the typeclass that overrides `·[·]`.



/- SECTION: Non-Empty Lists -/

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def cuteCats : NonEmptyList String := { head := "Ninja", tail := ["Dolly"] }

instance [ToString α] : ToString (NonEmptyList α) where
  toString | ⟨h, t⟩ => toString (h :: t)
#eval { head := 1, tail := [2, 3, 4] : NonEmptyList Nat }

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | { head := x, tail := _ },  0      => x
  | { head := _, tail := xs }, n + 1  => xs.get? n

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem zeroSafeForCats : cuteCats.inBounds 0 := by simp
--theorem twoNotSafeForCats : ¬ (cuteCats.inBounds 2) := by simp -- My copy of Lean hates this for some reason

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0     => xs.head
  | n + 1 => xs.tail[n] -- `ok` is used as an implicit argument in Lean's `·[·]` lookup.



/- SECTION: Overriding indexing -/

-- Lean provides this typeclass:
#check GetElem

/- Lean provides:
` class GetElem                                                       `
`   (collection : Type)                                               ` -- Need a collection to index into
`   (index : Type)                                                    ` -- Need an indexing type
`   (element : outParam Type)                                         ` -- Need a type of elements inside the collection
`   (inBounds : outParam (collection → index → Prop))                 ` -- Need a type of proofs for "being in bounds"
` where                                                               `
`   getElem : (c : collection) → (i : index) → inBounds c i → element ` -- Given a `c : collection`, an `i : index` and proof `: inBounds c i` that `i` is a valid index into `c`, gimme an `: element`.
-/

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

#eval cuteCats[0]
#eval cuteCats[1]
--#eval cuteCats[2]  -- Failed to prove index is valid :)

def cuterCats : List String := ["Ninja", "Dolly"]
def cutestCats : Point String := ⟨"Ninja", "Dolly"⟩

instance
  : GetElem (List α) Pos α
      (fun αs i => (αs.length > 0) ∧ (i.toNat < αs.length))
        -- A proof that `i` is in bounds for `α` is a proof that
        --  `αs.length > 0` and that `i.toNat < αs.length`.
where
  getElem αs i ok := αs[i.toNat]  -- `ok` implicitly used in `·[·]`
#eval cuterCats[(1 : Pos)]

instance
  : GetElem (Point α) Bool α
    (fun _ _ => true)
      -- A proof that `b` is in bounds for `p` is vacuous.
where
  getElem | ⟨x, _⟩, false, _ => x | ⟨_, y⟩, true, _ => y
#eval cutestCats[false]
