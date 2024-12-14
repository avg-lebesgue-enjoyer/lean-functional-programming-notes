/- @file Notes/Chapter5/Sec1TypeClass.lean
 - @src https://lean-lang.org/functional_programming_in_lean/monads/class.html
 -/

/- IMPORTS: State -/

-- The `State` type
def State (σ α : Type) := σ → σ × α
-- State-specific structure
def get : State σ σ :=            -- Read the current state (by chucking it in the output field)
  fun s => (s, s)
def set (s : σ) : State σ Unit := -- Overwrite the current state (and discard the value)
  fun _ => (s, ())

/- IMPORTS: WithLog -/

-- The `WithLog` type
structure WithLog (logs : Type) (α : Type) where
  log   : List logs
  value : α
deriving Repr

/- IMPORTS: BinTree -/

inductive BinTree (α : Type) : Type where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α



/- SECTION: The Monad Type Class -/

class Monad' (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β



/- SECTION: General Monad operations -/

def mapM [Monad m] (f : α → m β) : List α → m (List β)
| []        => pure []
| (a :: as) => do
  let b  <- f a
  let bs <- mapM f as
  pure $ b :: bs

#check State

instance : Monad (State σ) where
  pure a    := fun s =>
    (s, a)
  bind sa f := fun s =>
    let (s', a) := sa s
    ; f a s'

-- Increments the current `Int` state by some value,
--  and returns the old value.
def increment (howMuch : Int) : State Int Int :=
  get               >>= fun i =>
  set (i + howMuch) >>= fun () =>
  pure i

#eval mapM increment [1, 2, 3, 4, 5] 0

instance : Monad (WithLog μ) where
  pure a := ⟨[], a⟩
  bind a f :=
    let ⟨aLogs, aValue⟩ := a
    let ⟨bLogs, bValue⟩ := f aValue
    ; ⟨aLogs ++ bLogs, bValue⟩

-- Logs a value if it is even; otherwise makes no logs.
-- Leaves the value itself alone.
def saveIfEven (i : Int) : WithLog Int Int :=
  (if i % 2 == 0 then ⟨[i], ()⟩ else pure ()) >>= fun () => pure i

#eval mapM saveIfEven [0, 1, 2, 3, 4, 5, 6, 7, 8]



/- SECTION: The Identity Monad -/

def Id' (t : Type) : Type := t -- The name `Id` is already reserved for pretty much this

instance : Monad Id' where
  pure      := id
  bind x f  := f x

#eval mapM (· + 1) [1, 2, 3]      (m := Id)



/- SECTION: Exercises -/

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | leaf          => pure leaf
  | branch l x r  => do
    let l' <- mapM f l
    let x' <-      f x
    let r' <- mapM f r
    ; pure $ branch l' x' r'
