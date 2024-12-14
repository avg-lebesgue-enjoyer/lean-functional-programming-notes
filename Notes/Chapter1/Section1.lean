/- @file Notes/Chapter1/Section1.lean
 - @src https://lean-lang.org/functional_programming_in_lean/getting-to-know/evaluating.html
 -/

/- SECTION: Evaluating expressions -/

#eval 1
#eval 1 + 2
#eval 1 + 2 * 5
#eval String.append "Hello, " "World!" -- function application like in Haskell
#eval String.append "great " (String.append "oak " "tree")
#eval if true then "yeppo" else "nope mate" -- `if_then_else_` as per Haskell
