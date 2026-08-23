import Examples.Lambda
import Tests.Basic

open Parser Parser.Utf8 Term

-- variable
#guard term.runOption "x" == some (.var "x")

-- lambda
#guard term.runOption "\\x. x" == some (.lam "x" (.var "x"))

-- application
#guard term.runOption "f x" == some (.app (.var "f") (.var "x"))

-- left-associative application
#guard term.runOption "f x y"
    == some (.app (.app (.var "f") (.var "x")) (.var "y"))

-- nested lambda
#guard term.runOption "\\x. \\y. x"
    == some (.lam "x" (.lam "y" (.var "x")))

-- lambda body extends right
#guard term.runOption "\\f. f x"
    == some (.lam "f" (.app (.var "f") (.var "x")))

-- parenthesized lambda in application
#guard term.runOption "(\\x. x) y"
    == some (.app (.lam "x" (.var "x")) (.var "y"))

-- church numeral
#guard term.runOption "\\f. \\x. f (f x)"
    == some (.lam "f" (.lam "x" (.app (.var "f") (.app (.var "f") (.var "x")))))

-- negative: empty
#guard term.runOption "" == none

-- negative: lone backslash
#guard term.runOption "\\" == none
