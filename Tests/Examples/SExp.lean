import Examples.SExp
import Tests.Basic

open Parser SExp

#guard sexp.runResult? (toText "hello") == some (.atom "hello")

#guard sexp.runResult? (toText "(a b)") == some (.pair (.atom "a") (.atom "b"))

#guard sexp.runResult? (toText "(a b c)")
    == some (.pair (.atom "a") (.pair (.atom "b") (.atom "c")))

#guard sexp.runResult? (toText "(a (b c))")
    == some (.pair (.atom "a") (.pair (.atom "b") (.atom "c")))
