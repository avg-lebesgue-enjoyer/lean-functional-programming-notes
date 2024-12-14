/- @file Notes/Chapter5/Sec2Example.lean
 - @src https://lean-lang.org/functional_programming_in_lean/monads/arithmetic.html
 -/

/- SECTION: The Reader monad-/

-- The `State σ` monad is `σ → σ × -`, which permits reading and writing to an external
--  variable `σ` in addition to the passed datatype `-`.
-- If you only need to *read* that value `σ`, then the returned `σ` (as in `σ × -`) is
--  irrelevant, so you may as well reduce complexity by getting rid of it. The result
--  is the **reader monad** `σ → -`.
def Reader (ρ : Type) (α : Type) : Type := ρ → α
-- The action `read : ρ → ρ` puts us into the monad.
def read : Reader ρ ρ := fun r => r
-- `pure` does what you think it does
def Reader.pure (a : α) : Reader ρ α := fun _ => a
-- `bind` is this:
def Reader.bind (ra : Reader ρ α)  (f : α → Reader ρ β) : Reader ρ β :=
  -- type signature: `(ra : ρ → α) → (f : α → ρ → β) → ρ → β`
  fun r =>
    f (ra r)  r

instance : Monad (Reader ρ) where
  pure := Reader.pure
  bind := Reader.bind
