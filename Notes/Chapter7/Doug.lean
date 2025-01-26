/-! **FILE** `Notes/Chapter7/Doug.lean`
    **SRC**  https://lean-lang.org/functional_programming_in_lean/monad-transformers/reader-io.html
    The `doug` command-line application for printing a file tree.
-/

/- IMPORTS: -/
-- (none)



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



/- SECTION: `ConfigIO'` -/

/-- `IO` augmented by `ReaderT` with a read-only global variable `: Config`. -/
abbrev ConfigIO : Type → Type := ReaderT Config IO



/- SECTION: `Entry` type and associated helpers -/

/-- A `file` or `dir`ectory to be shown by `doug`. -/
inductive Entry where
  | file : String → Entry
  | dir  : String → Entry
@[match_pattern] def file := Entry.file
@[match_pattern] def dir  := Entry.dir

/--
  In the current `ConfigIO` context, convert a `path : System.FilePath` to an `Option Entry`.

  **Returns `: ConfigIO' (Option Entry)`**
    - `none`, indicating navigation-style directiories `.` or `..`
    - `some (dir _)`,  indicating a directory
    - `some (file _)`, indicating a file
-/
def toEntry (path : System.FilePath) : ConfigIO (Option Entry) := do
  match path.components.getLast? with
  | none                  => pure <| some <| dir ""
  | some "." | some ".."  => pure none
  | some name             =>
    if name.toList.head? = some '.'  ∧  ¬ (← read).printDotfiles -- don't print dotfiles if so configured
    then pure <| none
    else pure <| some <| (if (← path.isDir) then dir else file) <| name


/-- Show the `fileName` of an `Entry.file`. -/
def showFileName (fileName : String) : ConfigIO Unit := do
  IO.println ((← read).fileName fileName) -- implicit coersion from `IO Unit` to `ConfigIO' Unit`

/-- Show the `dirName` of an `Entry.dir`ectory. -/
def showDirName (dirName : String) : ConfigIO Unit := do
  IO.println ((← read).dirName dirName) -- implicit coersion from `IO Unit` to `ConfigIO' Unit`



/- SECTION: Main worker `dirTree` -/

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
  match ← toEntry path with
  | none             => pure ()
  | some (file name) => showFileName name
  | some (dir  name) =>
    showDirName name
    let contents ← path.readDir -- implicit coersion `IO ⇝ ConfigIO'`
    withReader Config.inDirectory <|
      doList contents.toList fun d =>
        dirTree d.path



/- LAUNCH: `main` -/

def main (args : List String) : IO UInt32 := do
  match configFromArgs args with
  | none =>
    IO.eprintln s!"Bad argument(s) {" ".separate args}\n"
    IO.eprintln usage
    pure 1
  | some config =>
    dirTree (← IO.currentDir) config
    pure 0
