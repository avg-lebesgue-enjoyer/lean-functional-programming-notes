/- @file Notes/Chapter2/Sec1Running.lean
 - @src https://lean-lang.org/functional_programming_in_lean/hello-world/running-a-program.html
 -/

/- SECTION: how 2 run -/

/- To run this file, in the command line enter
    `lean --run Sec1Running.lean`
  which will compile this file and run `main : IO Unit` from this file.
-/
def helloWorld : IO Unit :=
  IO.println "Hello, world!"



/- SECTION: `do` notation -/

-- `do` notation works just like it does in Haskell. Same monad under the hood.
def doer : IO Unit := do
  let stdin  ← IO.getStdin  -- `stdin` stream
  let stdout ← IO.getStdout -- `stdout` stream. `IO.println` really points to `IO.getStdout.println`, for instance
  stdout.putStrLn "Pls give name"
  let name ← (fun s => s.dropRightWhile Char.isWhitespace) <$> stdin.getLine
  stdout.putStrLn $ "Hello, " ++ name ++ " :)"
  return ()



/- LAUNCH -/

def main : IO Unit := doer
