import Examples.Lambda
import Tests.Basic

open Parser Term

-- variable
#guard term.runResult? (toText "x") == some (.var "x")

-- lambda
#guard term.runResult? (toText "\\x. x") == some (.lam "x" (.var "x"))

-- application
#guard term.runResult? (toText "f x") == some (.app (.var "f") (.var "x"))

-- left-associative application
#guard term.runResult? (toText "f x y")
    == some (.app (.app (.var "f") (.var "x")) (.var "y"))

-- nested lambda
#guard term.runResult? (toText "\\x. \\y. x")
    == some (.lam "x" (.lam "y" (.var "x")))

-- lambda body extends right
#guard term.runResult? (toText "\\f. f x")
    == some (.lam "f" (.app (.var "f") (.var "x")))

-- parenthesized lambda in application
#guard term.runResult? (toText "(\\x. x) y")
    == some (.app (.lam "x" (.var "x")) (.var "y"))

-- church numeral
#guard term.runResult? (toText "\\f. \\x. f (f x)")
    == some (.lam "f" (.lam "x" (.app (.var "f") (.app (.var "f") (.var "x")))))

-- negative: empty
#guard term.runResult? (toText "") == none

-- negative: lone backslash
#guard term.runResult? (toText "\\") == none
