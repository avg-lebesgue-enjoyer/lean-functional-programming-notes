/- @file Notes/Chapter7/Sec2Bob.lean
 - @src https://lean-lang.org/functional_programming_in_lean/monad-transformers/transformers.html
 -/
namespace ν

/- SECTION: What is a Monad Transformer? -/

-- A monad transformer consists of the following:
-- [1.] A definition/datatype `T` that takes a monad as an argument.
--   Its type should be `⋯ → (Type u → Type v) → Type u → Type v`.
-- [2.] A `Monad` instance for `T m` which relies on a `[Monad m]` instance.
-- [3.] A `MonadLift m (T m)` instance that translates actions `: m α` to actions
--   `: T m α`.
-- Furthermore, all the relevant stuff should be `Lawful`:
-- [4.] There should be a proof `: [LawfulMonad m] → [LawfulMonad (T m)]`.
-- [5.] `∀ x, monadLift ((pure (m := m)) x) = (pure (m := T m)) x`
-- [6.] `∀ x f, monadLift (x >>= f) = monadLift x >>= (monadLift ∘ f)`



/- SECTION: `OptionT`, and a sample program for it -/

-- [1.] Definition of `OptionT`
abbrev OptionT  : (Type u → Type v) → Type u → Type v := (· ∘ Option)
def OptionT.mk  : m (Option α) → OptionT m α := id
def OptionT.run : OptionT m α → m (Option α) := id

-- [2.]
def OptionT.pure [Monad m] : α → OptionT m α
  | a => (Pure.pure (f := m)) (some a)
  -- Alternatively, `(Pure.pure (some a) : m (Option _))`

-- [2.]
def OptionT.bind [Monad m] : OptionT m α → (α → OptionT m β) → OptionT m β :=
  fun moa f =>
    (Bind.bind (m := m)) moa <| fun oa =>
      match oa with
      | none   => (Pure.pure (f := m)) none
      | some a => f a

-- [2.] Promoting `Monad` instances
instance [Monad m] : Monad (OptionT m) where
  pure := OptionT.pure
  bind := OptionT.bind

-- [3.] A `MonadLift` instance
instance [Monad m] : MonadLift m (OptionT m) where
  -- `: m α → OptionT m α`
  monadLift := fun ma =>
    (Functor.map (f := m)) some ma

-- [4.]
theorem OptionT.id_map.{u_1}
  [Monad m] [law : LawfulMonad m]
  : ∀ {α : Type u_1} (x : OptionT m α), id <$> x = x
  := sorry
  -- by
  --   intro α moa
  --   show OptionT.bind moa (pure ∘ id) = moa
  --   have comp_id : ∀ {β : Type u_1} {γ : Type u_2} (f : β → γ), f ∘ id = f := by
  --     intros
  --     funext
  --     rfl
  --   rw [comp_id]
  --   unfold OptionT.bind
  --   have match_pure_comm
  --     : ∀ (oa : Option α),
  --       (match oa with | none => pure none | some a => pure a) = (pure oa : m (Option α))
  --     := by
  --       intro oa ; cases oa <;> rfl
  --   show (Bind.bind (m := m)) moa (fun (oa : Option α) => match oa with | none => pure none | some a => pure a)
  --     = moa
  --   conv => { lhs; rhs; intro; rw [match_pure_comm] }
  --   show moa.run >>= pure = moa.run
  --   have : (id : Option α → Option α) = (fun a => a) := rfl
  --   rw [law.bind_pure_comp]
  --   have it := law.id_map (α := Option α)
  --   rw [this] at it
  --   rw [it]

-- [4.] Check `LawfulMonad` gets inherited
instance [Monad m] [law : LawfulMonad m] : LawfulMonad (OptionT m) where
  map_const := rfl
  id_map := OptionT.id_map -- pain in the ass
  seqLeft_eq := sorry -- fuck this
  seqRight_eq := sorry -- fuck this
  pure_seq := sorry -- fuck this
  bind_pure_comp := sorry -- fuck this
  bind_map := sorry -- fuck this
  pure_bind := sorry -- fuck this
  bind_assoc := sorry -- FUCK this

-- [5.], [6.]: cba
instance [Monad m] : MonadLift m (OptionT m) where
  monadLift action := OptionT.mk do
    pure (some (← action))

instance [Monad m] : Alternative (OptionT m) where
  failure := OptionT.mk (pure none)
  orElse x ly := OptionT.mk do
    match ← x with
    | none        => ly ()
    | some result => pure (some result)

def getSomeInput : OptionT IO String := do
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trim
  if trimmed == "" then
    failure
  else pure trimmed

structure UserInfo where
  name         : String
  favouriteCat : String

def getUserInfo : OptionT IO UserInfo := do
  IO.println "Give name"
  let name ← getSomeInput
  IO.println "Give favourite cat"
  let cat ← getSomeInput
  pure ⟨name, cat⟩

def interact : IO Unit := do
  match ← getUserInfo with
  | none => IO.eprintln "Damnit dude"
  | some ⟨name, cat⟩ => IO.println s!"Hi {name} who likes {cat}"



/- SECTION: `ExceptT` -/

-- This is pretty much the same as `OptionT`. `ExceptT PUnit` is isomorphic to `OptionT`.
def ExceptT (ε : Type u) (m : Type u → Type v) : Type u → Type v := m ∘ Except ε

def ExceptT.mk  {ε α : Type u} (mea : m (Except ε α)) : ExceptT ε m α  := mea
def ExceptT.run {ε α : Type u} (ema : ExceptT ε m α)  : m (Except ε α) := ema

instance
  {ε : Type u} {m : Type u → Type v} [Monad m]
  : Monad (ExceptT ε m)
  where
    pure a := ExceptT.mk (pure (Except.ok a))
    bind mea f := ExceptT.mk do
      match ← mea with
      | .ok    a => f a
      | .error e => pure (.error e)

instance [Monad m] : MonadLift (Except ε) (ExceptT ε m) where
  monadLift ea := ExceptT.mk (pure ea)

instance [Monad m] : MonadLift m (ExceptT ε m) where
  monadLift ma := ExceptT.mk <| .ok <$> ma
    -- This is what I came up with; it's probably existentially equivalent:
    -- `ExceptT.mk do         `
    -- `  (pure ∘ .ok) (← ma) `



/- SECTION: `MonadExcept` -/

/- Lean supports
  ` class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where `
  `   throw    : ε → m α                                                  `
  `   tryCatch : m α → (ε → m α) → m α                                    `
-/

inductive Err where
  | divByZero : Err
  | nAN       : String → Err

def divBackend [Monad m] [MonadExcept Err m] (n d : Int) : m Int :=
  if d = 0 then throw .divByZero else pure (n / d)

def asNumber [Monad m] [MonadExcept Err m] (s : String) : m Int :=
  match s.toInt? with
  | none   => throw (.nAN s)
  | some i => pure i

def divFrontend [Monad m] [MonadExcept Err m] (n d : String) : m String := do
  try
    pure (toString (← divBackend (← asNumber n) (← asNumber d)))
  catch
    | .divByZero => pure "Fuck mate, you divided by zero; no bueno bruda"
    | .nAN s     => pure s!"Mate, {s} is not a numba"
-- Here, `try (t : m α) catch (c : ε → m α)` is sugar for `tryCatch t c`



/- SECTION: `StateT` -/

def StateT (σ : Type u) (m : Type u → Type v) : Type u → Type (max u v) :=
  fun α => σ → m (α × σ)

instance [Monad m] : Monad (StateT σ m) where
  pure a := fun s => pure (a, s)
  bind sma f :=
    fun s => do
      let (a, s') ← sma s
      f a s'

-- Lean supports these:
/-
  ` class MonadState                  `
  `   (σ : outParam (Type u))         `
  `   (m : Type u → Type v)           `
  `   : Type (max (u + 1) v) where    `
  `     get : m σ                     `
  `     set : σ → m PUnit             `
  `     modifyGet : (σ → α × σ) → m α `
-- and this, which uses `modifyGet` without actually providing a meaningful return value:
  ` def modify.{u, v}                         `
  `   : {σ : Type u}                          `
  `   → {m : Type u → Type v}                 `
  `   → [inst : MonadState σ m]               `
  `   → (σ → σ)                               `
  `   → m PUnit                               `
  `   := fun {σ} {m} [MonadState σ m] f =>    `
  `     modifyGet fun s => (PUnit.unit, f s)  `
-/
#print modify



end ν
/- LAUNCH: -/

def main : IO Unit := ν.interact
