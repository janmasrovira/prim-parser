import Examples.SExp
import Tests.Basic

open Parser Parser.Utf8 SExp

#guard sexp.runOption "hello" == some (.atom "hello")

#guard sexp.runOption "(a b)" == some (.pair (.atom "a") (.atom "b"))

#guard sexp.runOption "(a b c)"
    == some (.pair (.atom "a") (.pair (.atom "b") (.atom "c")))

#guard sexp.runOption "(a (b c))"
    == some (.pair (.atom "a") (.pair (.atom "b") (.atom "c")))
