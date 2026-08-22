import PrimParser

open Parser Parser.Char

namespace Balanced

def group : StringParser Error conditional PUnit :=
  fix (fun rec => gdo
    char '('
    skipMany rec
    char ')')

/-- A sequence of balanced groups followed by end-of-input, e.g. `()()`, `()(())`. -/
def balanced : StringParser Error fallible PUnit := gdo
  skipMany group
  eof

end Balanced
