/- @file Notes/Chapter7/Sec1Combining.lean
 - @src https://lean-lang.org/functional_programming_in_lean/monad-transformers/reader-io.html
 -/

/- SECTION: Helpers -/

/-- Intersperses a `List String` with a separator `sep : String`. -/
def String.separate (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: y :: zs => x ++ sep ++ sep.separate (y :: zs)

def doList [Applicative m] : List α → (α → m Unit) → m Unit
  | [],      _          => pure ()
  | x :: xs, actionDoer =>
    actionDoer x *> doList xs actionDoer



/- SECTION: IO-facing setup portion of code -/

/-- A basic `Config`uration for using `doug`. -/
structure Config : Type where
  useASCII      : Bool   := false
  printDotfiles : Bool   := true
  currentPrefix : String := ""
deriving Repr

/-- Usage information for `doug`. Displayed to the user when bad command-line arguments are provided. -/
def usage : String :=
  "Usage: doug [--ascii] \
   Options: \n\
   \t--ascii\tUse ASCII characters to display the directory structure\n\
   \t--a\tShow hidden files"

/--
  Convert a command-line `List` of `String` arguments into a `Config`uration for use with `doug`.
  Returns `Option.none` in the case of badly formatted command-line arguments.
-/
def configFromArgs : List String → Option Config
  | []          => .some { } -- defaults
  | "--ascii" :: args => configFromArgs args >>= ({· with useASCII      := true  : Config})
  | "--a"     :: args => configFromArgs args >>= ({· with printDotfiles := true  : Config})
  | _           => .none



/- SECTION: `ConfigIO` -/

def ConfigIO (α : Type) : Type :=
  Config → IO α

instance : Monad ConfigIO where
  pure x _ := pure x
  bind x f config := do f (← x config) config

def ConfigIO.run (action : ConfigIO α) (config : Config) : IO α :=
  action config

def currentConfig : ConfigIO Config := fun config => pure config

def locally (update : Config → Config) (action : ConfigIO α) : ConfigIO α :=
  fun config => action (update config)

/-- Coerce an `(action : IO α)` into a `ConfigIO α`. -/
def runIO (action : IO α) : ConfigIO α :=
  fun _ => action



/- SECTION: `Config` helpers -/
namespace Config
  /-- Prefix to be added before showing an `Entry.dir`ectory. -/
  def dirPrefix (config : Config) : String :=
    if config.useASCII then "|  " else "│  "
  /-- Prefix to be added before showing an `Entry.file`. -/
  def filePrefix (config : Config) : String :=
    if config.useASCII then "|--" else "├──"

  /-- Update the given `Config` with an extra directory prefix. Used when descending into a directory. -/
  def inDirectory (config : Config) : Config :=
    {config with currentPrefix := config.dirPrefix ++ " " ++ config.currentPrefix}

  /-- Display the `fileName` of some file. -/
  def fileName (config : Config) (fileName : String) : String :=
    s!"{config.currentPrefix}{config.filePrefix} {fileName}"
  /-- Display the `dirName` of some directory. -/
  def dirName (config : Config) (dirName : String) : String :=
    s!"{config.currentPrefix}{config.filePrefix} {dirName}/"
end Config



/- SECTION: Main worker `dirTree` -/

/-- A `file` or `dir`ectory to be shown by `doug`. -/
inductive Entry where
  | file : String → Entry
  | dir  : String → Entry
@[match_pattern] def file := Entry.file
@[match_pattern] def dir  := Entry.dir

/--
  In the current `IO` context, convert a `path : System.FilePath` to an `Option Entry`.

  **Returns `: IO (Option Entry)`**
    - `none`, indicating navigation-style directiories `.` or `..`
    - `some (dir _)`,  indicating a directory
    - `some (file _)`, indicating a file
-/
def toEntry (path : System.FilePath) : IO (Option Entry) := do
  match path.components.getLast? with
  | none                  => pure <| some <| dir ""
  | some "." | some ".."  => pure none
  | some name             => pure <| some <| (if (← path.isDir) then dir else file) <| name

/-- Show the `fileName` of an `Entry.file`. -/
def showFileName (fileName : String) : ConfigIO Unit := do
  runIO <| IO.println ((← currentConfig).fileName fileName)

/-- Show the `dirName` of an `Entry.dir`ectory. -/
def showDirName (dirName : String) : ConfigIO Unit := do
  runIO <| IO.println ((← currentConfig).dirName dirName)

/--
  Print a directory subtree rooted at a given `System.FilePath`.
  It may not be a *tree* if the user's OS is shit, so this is a `partial` IO action.

  **Param `(config : Config)`**
    The configuration used for printing.

  **Param `(path : System.FilePath)`**
    The root of the subtree to be printed.

  **Returns `: IO Unit`**
    (Does the effect.)
-/
partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← runIO (toEntry path) with
  | none             => pure ()
  | some (file name) => showFileName name
  | some (dir  name) =>
    showDirName name
    let contents ← runIO path.readDir
    locally (Config.inDirectory) <|
      doList contents.toList fun d =>
        dirTree d.path



/- LAUNCH: `mainOld` -/

def mainOld (args : List String) : IO UInt32 := do
  match configFromArgs args with
  | none =>
    IO.eprintln s!"Bad argument(s) {" ".separate args}\n"
    IO.eprintln usage
    pure 1
  | some config =>
    ConfigIO.run (dirTree (← IO.currentDir)) config
    pure 0



/- SECTION: But what actually *is* `ConfigIO`, and how does it generalise? -/

/--
  A monad transformer that adds a global variable with read privileges.

  **Param `(ρ : Type u)`**
    The type with the global variable to be read from.

  **Param `(m : Type u → Type v)`**
    The monad to overload with the global variable.

  **Returns `: Type u → Type (max u v)`**
    A new monad which may read from a global variable of type `ρ` and otherwise
    subsumes the effects of `m`.
-/
def ReaderT'
  (ρ : Type u) (m : Type u → Type v)
  : Type u → Type (max u v) :=
  fun α =>
  ρ → m α

-- NOTE: `ConfigIO` is really `IO` augmented with `Config → ·`.
abbrev ConfigIO'' := ReaderT Config IO

-- `#check read` -- This is `currentConfig`; `MonadReader` is a substructure of `ReaderT`.

instance [Monad m] : Monad (ReaderT' ρ m) where
  pure a := fun _ => pure a -- `pure` is constant on the environment argument
  bind a f := fun env =>
    a env >>= (f · env) -- environment gets instantiated on each branch of the underlying `bind`

/- Lean has
  ` class MonadLift (m : Type u → Type v) (n : Type u → Type w) where `
  `   monadLift : {α : Type u} → m α → n α                            `
-- which is used to coerce ("lift") an `m`-action to an `n`-action.
-/
instance : MonadLift m (ReaderT' ρ m) where
  monadLift a := fun _ => a

/- Lean supports
  ` class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where `
  `   withReader {α : Type u} : (ρ → ρ) → m α → m α                           `
  ` export MonadWithReader (withReader)                                       `
-- which is used for our `locally` function above.
-/
instance : MonadWithReader ρ (ReaderT' ρ m) where
  withReader update action := action ∘ update -- do the action *after* you update
  -- `withReader update action` reads idiomatically as "with the `update`, do your `action`".



-- Time to rewrite `doug` with `ReaderT`.

/- SECTION: `ConfigIO'` -/

/-- `IO` augmented by `ReaderT` with a read-only global variable `: Config`. -/
abbrev ConfigIO' : Type → Type := ReaderT Config IO

def ConfigIO'.run (action : ConfigIO' α) (config : Config) : IO α :=
  action config

/- SECTION: Get entry in context -/

/--
  In the current `IO` context, convert a `path : System.FilePath` to an `Option Entry`.

  **Returns `: ConfigIO' (Option Entry)`**
    - `none`, indicating navigation-style directiories `.` or `..`
    - `some (dir _)`,  indicating a directory
    - `some (file _)`, indicating a file
-/
def toEntry' (path : System.FilePath) : ConfigIO' (Option Entry) := do
  match path.components.getLast? with
  | none                  => pure <| some <| dir ""
  | some "." | some ".."  => pure none
  | some name             =>
    if name.toList.head? = some '.'  ∧  ¬ (← read).printDotfiles -- don't print dotfiles if so configured
    then pure <| none
    else pure <| some <| (if (← path.isDir) then dir else file) <| name

/- SECTION: Main worker `dirTree` -/

/-- Show the `fileName` of an `Entry.file`. -/
def showFileName' (fileName : String) : ConfigIO' Unit := do
  IO.println ((← read).fileName fileName) -- implicit coersion from `IO Unit` to `ConfigIO' Unit`

/-- Show the `dirName` of an `Entry.dir`ectory. -/
def showDirName' (dirName : String) : ConfigIO' Unit := do
  IO.println ((← read).dirName dirName) -- implicit coersion from `IO Unit` to `ConfigIO' Unit`

/--
  Print a directory subtree rooted at a given `System.FilePath`.
  It may not be a *tree* if the user's OS is shit, so this is a `partial` IO action.

  **Param `(config : Config)`**
    The configuration used for printing.

  **Param `(path : System.FilePath)`**
    The root of the subtree to be printed.

  **Returns `: IO Unit`**
    (Does the effect.)
-/
partial def dirTree' (path : System.FilePath) : ConfigIO' Unit := do
  match ← toEntry' path with
  | none             => pure ()
  | some (file name) => showFileName' name
  | some (dir  name) =>
    showDirName' name
    let contents ← path.readDir -- implicit coersion `IO ⇝ ConfigIO'`
    withReader Config.inDirectory <|
      doList contents.toList fun d =>
        dirTree' d.path



/- LAUNCH: `main` -/

def main (args : List String) : IO UInt32 := do
  match configFromArgs args with
  | none =>
    IO.eprintln s!"Bad argument(s) {" ".separate args}\n"
    IO.eprintln usage
    pure 1
  | some config =>
    dirTree' (← IO.currentDir) config
    pure 0



/- EXERCISES: them -/

-- EXERCISE: Controlling the Display of Dotfiles
--    done

-- EXERCISE: Starting Directory as Argument
--    nah, I don't wanna
