# prim-parser: Total Parser Combinator Library

prim-parser is a total parser combinator library for Lean 4 that uses a graded
monad. [This blog post](https://blog.janmasrovira.org/blog/prim-parser/)
describes the library in detail, presents examples and compares it to similar
libraries.

## Structure

- `PrimParser/`: library code.
- `Examples/`: example parsers.
- `Tests/`: `#guard`-based compile-time tests.

## Build

```sh
lake build # build the library
lake build Tests # run the tests
```
