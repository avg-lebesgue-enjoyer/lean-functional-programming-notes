/- @file Notes/Chapter2/Sec2Steps.lean
 - @src https://lean-lang.org/functional_programming_in_lean/hello-world/step-by-step.html
 -/

/- SECTION: IO Actions vs Values -/

-- NOTE: any `#eval` or `#check` etc gets compiled into executed code!
#eval "HELLO!!!".dropRightWhile (· == '!')  -- NOTE: HOLY SHIT `·` IS `\.`, NOT `\cdot` `⬝` (`·⬝` fkn end me)
                                            --       ^^ this is fkn stupid Lean.
#eval "Hello.........         ".dropRightWhile (not ·.isAlphanum) -- so is the name `isAlphanum`. Camelcase or don't.

-- Takes `action` as a parameter, but doesn't execute it at pass-time...
def twice (action : IO Unit) : IO Unit := do
  action  -- executes it here
  action  -- and again

def countdown : Nat → List (IO Unit)
  | 0     => [IO.println "Blast Off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def executeActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | a :: as => do
    a
    executeActions as

def tMinus5 := executeActions ∘ countdown $ 5 -- NOTE: `∘` (`\circ`) is function composition



/- LAUNCH -/

def helloWorld : IO Unit := IO.println "Hello from Section 2.2 :)"

def main : IO Unit := tMinus5

#eval main
#check main
