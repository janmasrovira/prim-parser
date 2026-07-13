* prim-parser: Total Parser Combinator Library
prim-parser is a total parser combinator library for Lean 4 that uses a graded
monad. [[https://blog.janmasrovira.org/blog/prim-parser/][This blog post]] describes the library in detail, presents examples and compares
it to similar libraries.

** Structure
- ~PrimParser/~ -- library: ~Grade~, ~Parser~, combinators, graded monad typeclasses, ~gdo~ notation
- ~Examples/~ -- example parsers
- ~Tests/~ -- ~#guard~-based compile-time tests

** Build
#+begin_src sh
lake build # build the library
lake build Tests # run the tests
#+end_src
