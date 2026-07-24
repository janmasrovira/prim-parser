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

## FAQ

### Why depend on Mathlib?

Some people have asked why should this library depend on Mathlib. For the
following reasons, I think it makes sense to keep it as a dependency:

1. It doesn't slow down CI. We use
  [`leanprover/lean-action`](https://github.com/leanprover/lean-action), which
  downloads Mathlib prebuilt, so CI still runs in reasonable time (in about 2
  minutes at the time of writing this).
2. `Lattice` lemmas. Grades combine with `⊔` and `⊓`, and the `grade_by` proofs
  often rely on Mathlib's lattice lemmas.
3. `Monoid` is used in `LawfulGradedMonad`, `LawfulGradedApplicative`, `LawfulGradedFunctor`.
4. `List.Vector` is used for the fixed-count combinators, like `sepByN`.

If there is an elegant way to drop the Mathlib dependency without sacrificing
usability and compatibility, I'd be happy to adapt.
