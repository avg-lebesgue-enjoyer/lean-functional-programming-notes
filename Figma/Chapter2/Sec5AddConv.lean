/- @file Notes/Chapter2/Sec5AddConv.lean
 - @src https://lean-lang.org/functional_programming_in_lean/hello-world/conveniences.html
 -/

/- SECTION: Nested actions -/

-- This kinda sucks:
def sucks : IO Unit := do
  IO.print "Gimme some input: "
  let stdin ← IO.getStdin
  let repeatMe ← (·.dropRightWhile (·.isWhitespace)) <$> stdin.getLine
  IO.println $ "You said: " ++ repeatMe ++ " :)"
-- This is better
def better : IO Unit := do
  IO.print "Gimme some input: "
  -- The `(← IO.getStdin)` here immediately executes the `IO.getStdin` action, and binds
  --  the result to a temporary name (which I promise doesn't collide with any names that
  --  appear in your code).
  -- It does this by lifting the `(← IO.getStdin)` to the closest previous `do` block,
  --  and running it there. So, it desugars to `sucks`.
  -- This does mean that **SUCH CODE ALWAYS GETS RUN**, even if it's on a branch that
  --  "never executes".
  let repeatMe ← (·.dropRightWhile (·.isWhitespace)) <$> (← IO.getStdin).getLine
  IO.println $ "You said: " ++ repeatMe ++ " :)"



/- SECTION: Taking back control of whitespace in `do` blocks -/

set_option linter.unusedVariables false -- this does what you think it does

def gimmeMyWhitespaceBack : IO Unit := do { -- `{ ... }` denote a nested `do` block
  let stdin ← IO.getStdin; let stdout ← IO.getStdout; -- the `;` here separates actions/"lines" in a `do` block
  -- do some cool stuff with them...
  return ()
}
-- In essence, the `{ ... }`s and `;`s do what they do in C++.

set_option linter.unusedVariables true -- this does what you think it does



/- SECTION: `partial` functions -/

-- Defining a `partial` function allows for infinite recursion with no proof of termination.
partial def f : Nat → Nat := f


/- LAUNCH -/

def main : IO Unit := sucks
