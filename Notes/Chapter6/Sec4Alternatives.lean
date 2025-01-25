/- @file Notes/Chapter6/Sec4Alternatives.lean
 - @src https://lean-lang.org/functional_programming_in_lean/functor-applicative-monad/alternative.html
 -/

/- IMPORTS: `Validate` -/

import Notes.Chapter6.Sec2Applicatives



/- SECTION: Recovery From Failure -/

abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970
    : (birthYear : {y : Nat // 999 < y ∧ y < 1970})
    → String -- name, potentially empty
    → LegacyCheckedInput
  | humanAfter1970
    : (birthYear : {y : Nat // 1970 < y})
    → NonEmptyString -- name
    → LegacyCheckedInput
  | company
    : NonEmptyString -- company name
    → LegacyCheckedInput
deriving Repr

/- Validation rules for new users:
  [1.] All human users must provide a birth year that is four digits
  [2.] Users born prior to 1970 do not need to provide names
  [3.] Users born after 1970 must provide names
  [4.] Companies should enter `"FIRM"` as their year of birth
        and provide a company name
-/

/--
  Accepts the first result if it is `.ok`, or otherwise attempts to accept
  the second result. Errors are accumulated from both arguments if they both
  `.error`.

  **Param `a : Validate ε α`**
    This value will be accepted if it is `.ok`; otherwise, if it `.error`s,
    the parameter `b` will be tried.

  **Param `b : Unit → Validate ε α`**
    A (delayed-computation) value to use instead of `a` if `a` `.error`s.

  **Returns `: Validate ε α`**
    - If `a` is `.ok`, then `a`
    - If `a` is `.errors` but `b` is `.ok`, then `b`
    - If both `a` and `b` are `.errors`, then return `.errors` with the
        errors of `a` and `b` accumulated.
 -/
def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok x         => .ok x
  | .errors e₁ =>
    match b () with
    | .ok x       => .ok x
    | .errors e₂  => .errors (e₁ ++ e₂)

-- In fact, Lean has
#print OrElse
/-
  ` class OrElse.{u} (α : Type u) : Type u where  `
  `   orElse : α → (Unit → α) → α                 `
-/
-- so we really just made
instance : OrElse (Validate ε α) where
  orElse := Validate.orElse
-- Lean supports the overloaded notation
#check (· <|> ·)
-- with
--  `e₁ <|> e₂  :=  OrElse.orElse e₁ (fun () => e₂)`

/--
  Validate that a `condition` holds.

  **Param `(condition : Bool)`**
    The condition to validate.

  **Param `(field : Field)`**
    The `Field` to report an error for, should the `condition` not hold.

  **Param `(message : String)`**
    The message to report as an error, should the `condition` not hold.
-/
def checkThat
  (condition : Bool) (field : Field) (message : String)
  : Validate (Field × String) Unit :=
  if condition then pure () else reportError field message

/--
  Validate input data for a company.

  **Param `(input : RawInput)`**
    The input data to validate.

  **Returns `: Validate (Field × String) LegacyCheckedInput`**
    Validated input.
-/
def checkCompany
  (input : RawInput)
  : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") -- Validation rule [4.]
    (field := "Birth year")
    (message := "Birth year must be \"FIRM\" for a company.")
  *>  LegacyCheckedInput.company -- `ma *> mb` combines the effects of `ma` and `mb`, but ignores the value of `ma` in favour of the value of `mb`
  <$> checkName input.name
#check (· *> ·)

/--
  Validate a `value` against the subtype `{a : α // predicate a}` by checking if
  it satisfies some `[Decidable]` `predicate`.

  **Param `(value : α)`**
    Value to validate.

  **Param `(predicate : α → Prop)`**
    Predicate to check the `value` against.

  **Inst `[Decidable (predicate value)]`**
    Allows Lean to actually evalute `predicate value`.

  **Param `(error : ε)`**
    Error to report should `predicate value` be `false`.

  **Returns `: Validate ε {a : α // predicate a}`**
    A validated version of `value`, regarded as a term of `Subtype predicate`,
    and being `.errors [error]` iff `predicate value` is false.
-/
def checkSubtype
  {α ε : Type}
  (value : α)
  (predicate : α → Prop)
  [Decidable (predicate value)]
  (error : ε)
  : Validate ε {a : α // predicate a} :=
  if h : predicate value
  then .ok      ⟨value, h⟩
  else .errors  ⟨[error], (by simp)⟩

/-- Validate a human born before 1970. -/
def checkHumanBefore1970
  (input : RawInput)
  : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen $ fun year =>
    LegacyCheckedInput.humanBefore1970
    <$> checkSubtype year (fun x => 999 < x ∧ x < 1970)
          ("Year", "Year must be four digits and less than 1970.")
    <*> pure input.name

/-- tin -/
def checkHumanAfter1970
  (input : RawInput)
  : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen $ fun year =>
    LegacyCheckedInput.humanAfter1970
    <$> checkSubtype year (1970 < ·)
          ("Year", "Year must be greater than 1970.")
    <*> checkSubtype input.name (· ≠ "")
          ("Name", "Name must not be empty!")

/--
  Validates that the given `(input : RawInput)` matches any of the validation
  rules [1.], [2.], [3.], [4.].
 -/
def checkLegacyInput
  (input : RawInput)
  : Validate (Field × String) LegacyCheckedInput :=
  checkCompany input
  <|> checkHumanBefore1970 input
  <|> checkHumanAfter1970  input
-- that's clean af
#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "Goober"⟩
#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "999"⟩
#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "1900"⟩
#eval checkLegacyInput ⟨"", "1900"⟩
#eval checkLegacyInput ⟨"", "1970"⟩



/- SECTION: The `Alternative` Class -/

/- Lean has:
  ` class Alternative (m : Type → Type) extends Applicative m where `
  `   failure : m α                                                 `
  `   orElse  : m α → (Unit → m α) → m α                            `
-- Unsurprisingly,
  ` instance [Alternative m] : OrElse (m α) where `
  `   orElse := Alternative.orElse                `
-/

instance : Alternative Option where
  failure := .none
  orElse
    | .some a, _   => .some a
    | .none,   lmb => lmb ()

/- Lean has `guard` built-in. -/
def guard' [Alternative m] (p : Prop) [Decidable p] : m Unit :=
  if p then pure () else failure

/-- `Many α` is the type of *lazy lists over `α`*. -/
inductive Many (α : Type) : Type where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

#print Seq.seq

instance : Applicative Many where
  pure a := .more a (fun _ => .none)
  seq := Many.seq -- `seq : Many (α → β) → (Unit → Many α) → Many β`
    where Many.seq {α β : Type} (fs : Many (α → β)) (las : Unit → Many α) : Many β :=
    match fs with
    | .none => .none
    | .more f lfs =>
      match las () with
      | .none => .none
      | .more a las => .more (f a) (fun () => Many.seq (lfs ()) las)
instance : Alternative Many where
  failure := .none -- `: Many α`
  orElse := Many.orElse -- `: {α : Type} → Many α → (Unit → Many α) → Many α`
    where Many.orElse {α : Type} (as : Many α) (lbs : Unit → Many α) : Many α :=
    match as with
    | .more a las => .more a (fun () => Many.orElse (las ()) lbs)
    | .none       => lbs ()
instance : Monad Many where
  bind := Many.bind -- `: {α β : Type} → Many α → (α → Many β) → Many β`
    where Many.bind {α β : Type} (as : Many α) (f : α → Many β) : Many β :=
      match as with
      | .none => .none
      | .more a las => Alternative.orElse (f a) $ fun () => Many.bind (las ()) f
def Many.takeAll : Many α → List α
  | .none => []
  | .more a las => a :: (las ()).takeAll

def Many.countdown : Nat → Many Nat
  | 0       => .none
  | .succ n => .more n (fun () => countdown n)

def evenDivisors (n : Nat) : Many Nat := do
  let k ← Many.countdown (n + 1)
  guard (k % 2 = 0)
  guard (n % k = 0)
  pure k
-- This is sick af

#eval (evenDivisors 20).takeAll
#eval (evenDivisors 15).takeAll
#eval (evenDivisors 990).takeAll



/- EXERCISES: Improve validation friendliness -/
namespace ex
  inductive Validate (ε α : Type) : Type
    | ok    : α → Validate ε α
    | error : ε → Validate ε α
  instance {ε : Type} [Append ε] : Applicative (Validate ε) where
    pure a := .ok a
    seq vf lva := -- `seq : {α β : Type} → Validate ε (α → β) → (Unit → Validate ε α) → Validate ε β`
      match vf, lva () with
      | .ok f,      .ok a     => .ok (f a)
      | .ok _,     .error e₂  => .error e₂
      | .error e₁, .ok _      => .error e₁
      | .error e₁, .error e₂  => .error (e₁ ++ e₂)
  instance {α ε : Type} [Append ε] : OrElse (Validate ε α) where
    -- `orElse : Validate ε α → (Unit → Validate ε α) → Validate ε α`
    orElse va lvb :=
      match va with
      | .ok a => .ok a
      | .error e₁ =>
        match lvb () with
        | .ok b => .ok b
        | .error e₂ => .error (e₁ ++ e₂)

  def Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α
    | .ok a, _ => .ok a
    | .error e, f => .error (f e)

  instance : Repr Field where
    reprPrec := Repr.reprPrec (α := String)

  inductive TreeError' (ε : Type) : Type where
    | field : ε             → ε             → TreeError' ε
    | path  : String        → TreeError' ε  → TreeError' ε
    | both  : TreeError' ε  → TreeError' ε  → TreeError' ε
  deriving Repr
  instance {ε : Type} : Append (TreeError' ε) where
    append := .both
  def TreeError'.map {α β : Type} (f : α → β) : TreeError' α → TreeError' β
      | .both e₁ e₂ => .both (e₁.map f) (e₂.map f)
      | .path p e   => .path p (e.map f)
      | .field i m  => .field (f i) (f m)
  instance : Functor TreeError' where
    map := TreeError'.map
  abbrev TreeError : Type := TreeError' String

  /-! NOTE: Some stock errors -/
  def firmYearError : TreeError := .field "Year" "Year must be entered as \"FIRM\" for a company."
  def nameNonemptyError : TreeError := .field "Name" "Name must be nonempty."
  def yearNANError : TreeError := .field "Year" "Year must be a non-negative integer."
  def humanBefore1970YearError : TreeError := .field "Year" "Year must be in the range `999 < year < 1970`."
  def humanAfter1970YearError : TreeError := .field "Year" "Year must be `> 1970`."

  instance : Append Unit where
    append _ _ := ()

  def checkThat
    (condition : Bool)
    : Validate Unit Unit :=
    if condition then pure () else .error ()

  def checkSubtype
    {α ε : Type}
    (value : α)
    (predicate : α → Prop)
    [Decidable (predicate value)]
    (error : ε)
    : Validate ε { a : α // predicate a } :=
    if h : predicate value
    then  .ok   ⟨value, h⟩
    else  .error error

  def checkYearIsNat (year : String) (error : ε) : Validate ε Nat :=
    match year.trim.toNat? with
    | .none   => .error error
    | .some y => .ok y

  def Validate.overrideError (vea : Validate ε α) (newError : ε') : Validate ε' α
    := vea.mapErrors (fun _ => newError)

  def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
    match val with
    | .ok a     => next a
    | .error e  => .error e

  /- Validation rules for new users:
    [1.] All human users must provide a birth year that is four digits
    [2.] Users born prior to 1970 do not need to provide names
    [3.] Users born after 1970 must provide names
    [4.] Companies should enter `"FIRM"` as their year of birth
          and provide a company name
  -/

  #print checkCompany
  def checkCompany
    (input : RawInput)
    : Validate TreeError LegacyCheckedInput :=
    (checkThat (input.birthYear == "FIRM")).overrideError firmYearError -- [4.]
    *> LegacyCheckedInput.company
    <$> checkSubtype input.name (· ≠ "") nameNonemptyError  -- [4.]
  #eval checkCompany ⟨"Johnny's Troll Groomers", "FIRM"⟩
  #eval checkCompany ⟨"", "FIRM"⟩
  #eval checkCompany ⟨"Johnny's Troll Groomers", "1990"⟩
  #eval checkCompany ⟨"", "1990"⟩

  def Function.pointwise (f : α → β) (combinator : β → γ → δ) (g : α → γ) : α → δ :=
    fun a => combinator (f a) (g a)
  #print Decidable
  instance
    {f : α → β} {g : α → γ} {combinator : β → γ → Prop}
    [inst : Decidable (combinator (f a) (g a))]
    : Decidable (Function.pointwise f combinator g a) := inst

  #print checkHumanBefore1970
  def checkHumanBefore1970
    (input : RawInput)
    : Validate TreeError LegacyCheckedInput :=
      LegacyCheckedInput.humanBefore1970
      <$> ((checkYearIsNat input.birthYear yearNANError).andThen $ fun year => -- [1.]
           (h ▸ checkSubtype year (Function.pointwise (999 < ·) (· ∧ ·) (· < 1970)) humanBefore1970YearError)) -- [1.]
      <*> pure input.name -- [2.]
      where h : {y // Function.pointwise (999 < ·) (· ∧ ·) (· < 1970) y} = {y // 999 < y ∧ y < 1970} := by {
        have : ∀ y : Nat, Function.pointwise (999 < ·) (· ∧ ·) (· < 1970) y ↔ 999 < y ∧ y < 1970 := by intro ; rfl
        conv => {
          lhs
          arg 1
          intro y
          rw [this y]
        }
      }
  #eval checkHumanBefore1970 ⟨"John", "1000"⟩
  #eval checkHumanBefore1970 ⟨"John", "999"⟩
  #eval checkHumanBefore1970 ⟨"John", "amon gus"⟩
  #eval checkHumanBefore1970 ⟨"", "1000"⟩
  #eval checkHumanBefore1970 ⟨"", "999"⟩
  #eval checkHumanBefore1970 ⟨"", "amon gus"⟩

  #print checkHumanAfter1970
  def checkHumanAfter1970
    (input : RawInput)
    : Validate TreeError LegacyCheckedInput :=
      LegacyCheckedInput.humanAfter1970
      <$> ((checkYearIsNat input.birthYear yearNANError).andThen $ fun year =>
            checkSubtype year (1970 < ·) humanAfter1970YearError) -- [1.]
      <*> checkSubtype input.name (· ≠ "") nameNonemptyError -- [3.]
  #eval checkHumanAfter1970 ⟨"John", "1971"⟩
  #eval checkHumanAfter1970 ⟨"John", "1970"⟩
  #eval checkHumanAfter1970 ⟨"John", "amon gus"⟩
  #eval checkHumanAfter1970 ⟨"", "1971"⟩
  #eval checkHumanAfter1970 ⟨"", "1970"⟩
  #eval checkHumanAfter1970 ⟨"", "amon gus"⟩

  def checkLegacyInput
    (input : RawInput)
    : Validate TreeError LegacyCheckedInput :=
        (checkCompany         input).mapErrors (.path "company")
    <|> (checkHumanBefore1970 input).mapErrors (.path "human born before 1970")
    <|> (checkHumanAfter1970  input).mapErrors (.path "human born after 1970")
  #eval checkLegacyInput ⟨"John", "1971"⟩
  #eval checkLegacyInput ⟨"John", "1970"⟩
  #eval checkLegacyInput ⟨"John", "1969"⟩
  #eval checkLegacyInput ⟨"John", "amon gus"⟩
  #eval checkLegacyInput ⟨"John", "FIRM"⟩
  #eval checkLegacyInput ⟨"", "1971"⟩
  #eval checkLegacyInput ⟨"", "1970"⟩
  #eval checkLegacyInput ⟨"", "1969"⟩
  #eval checkLegacyInput ⟨"", "amon gus"⟩
  #eval checkLegacyInput ⟨"", "FIRM"⟩

  theorem TreeError'.sizeOf_both_comm : ∀ (e₁ e₂ : TreeError' ε), sizeOf (e₁.both e₂) = sizeOf (e₂.both e₁) := by
    intros
    simp
    rw [Nat.add_right_comm]
  theorem TreeError'.sizeOf_both_left : ∀ (e₁ e₂ : TreeError' ε), sizeOf e₁ < sizeOf (e₁.both e₂) := by
    intro e₁ e₂
    simp
    unfold LT.lt instLTNat Nat.lt
    simp [Nat.add_comm _ 1]
  theorem TreeError'.sizeOf_both_right : ∀ (e₁ e₂ : TreeError' ε), sizeOf e₂ < sizeOf (e₁.both e₂) := by
    intros
    rw [TreeError'.sizeOf_both_comm]
    apply TreeError'.sizeOf_both_left
  theorem TreeError'.functor_map_eq_map {α β : Type} {f : α → β} (e : TreeError' α) : (f <$> e) = (e.map f) := by
    unfold Functor.map instFunctorTreeError'
    simp

  theorem TreeError'.map_sizeOf_hom {α β : Type} : ∀ (e : TreeError' α) (f : α → β), sizeOf (f <$> e) = sizeOf e := by
    intro e f
    induction e <;> rw [TreeError'.functor_map_eq_map] at *
    case field i m =>
      simp [TreeError'.map]
    case path p e ih =>
      simp [TreeError'.map, ih]
    case both e₁ e₂ ih₁ ih₂ =>
      simp [TreeError'.map, ih₁, ih₂]

  def TreeError'.report
    {ε : Type}
    [ToString ε] [Append ε]
    (indentation : ε)
    (me : TreeError' ε)
    : String := match me with
    | .both e₁ e₂ =>
      e₁.report indentation
      ++ "\n"
      ++ e₂.report indentation
    | .path p e   =>
      "If you are registering a " ++ p ++ ", then the following errors apply:\n"
      ++ ((indentation ++ ·) <$> e).report indentation
    | .field f m  => s!"{f}" ++ ": " ++ s!"{m}"
    termination_by me
    decreasing_by
      · show sizeOf e₁ < sizeOf (e₁.both e₂)
        apply TreeError'.sizeOf_both_left
      · show sizeOf e₂ < sizeOf (e₁.both e₂)
        apply TreeError'.sizeOf_both_right
      · show sizeOf ((fun x => indentation ++ x) <$> e) < sizeOf (path p e)
        simp [TreeError'.map_sizeOf_hom, Nat.lt_add_right]

  def test : Validate TreeError LegacyCheckedInput → String
    | .ok (.company c) => s!"Welcome, {c}"
    | .ok (.humanBefore1970 y n) => s!"Welcome, person born in the year {y} with name {n}"
    | .ok (.humanAfter1970 y n) => s!"Welcome, {n} ({y})"
    | .error e => e.report "\t"

  def main : IO Unit := do
    let gaming (x : String) := IO.println x >>= (fun () => IO.println "")
    gaming <| (test ∘ checkLegacyInput) ⟨"John", "1971"⟩
    gaming <| (test ∘ checkLegacyInput) ⟨"John", "1970"⟩
    gaming <| (test ∘ checkLegacyInput) ⟨"John", "1969"⟩
    gaming <| (test ∘ checkLegacyInput) ⟨"John", "amon gus"⟩
    gaming <| (test ∘ checkLegacyInput) ⟨"John", "FIRM"⟩
    gaming <| (test ∘ checkLegacyInput) ⟨"", "1971"⟩
    gaming <| (test ∘ checkLegacyInput) ⟨"", "1970"⟩
    gaming <| (test ∘ checkLegacyInput) ⟨"", "1969"⟩
    gaming <| (test ∘ checkLegacyInput) ⟨"", "amon gus"⟩
    gaming <| (test ∘ checkLegacyInput) ⟨"", "FIRM"⟩
  #eval main
  -- This was a pretty fun exercise; thank you :)

end ex
