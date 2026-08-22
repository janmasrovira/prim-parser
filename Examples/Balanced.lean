import PrimParser

open Parser

namespace Balanced

def group : Parser Error conditional PUnit :=
  fix (fun rec => gdo
    char '('
    skipMany rec
    char ')')

/-- A sequence of balanced groups followed by end-of-input, e.g. `()()`, `()(())`. -/
def balanced : Parser Error fallible PUnit := gdo
  skipMany group
  eof

end Balanced
