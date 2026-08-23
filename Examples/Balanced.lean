import PrimParser

open Parser Parser.Utf8

namespace Balanced

def group : Utf8Parser Error conditional PUnit :=
  fix (fun rec => gdo
    char '('
    skipMany rec
    char ')')

/-- A sequence of balanced groups followed by end-of-input, e.g. `()()`, `()(())`. -/
def balanced : Utf8Parser Error fallible PUnit := gdo
  skipMany group
  eof

end Balanced
