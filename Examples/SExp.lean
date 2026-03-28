import PrimParser

open Parser

inductive SExp where
  | atom (str : String)
  | pair (l r : SExp)
  deriving Repr, BEq

namespace SExp

private def listToPairs : List SExp → SExp
  | [x] => x
  | x :: xs => .pair x (listToPairs xs)
  | [] => .atom ""

private def isAtomChar (c : Char) : Bool := c.isAlphanum

def patom : Parser Error .conditional SExp :=
  .atom <$>ᵍ takeWhile1 isAtomChar

def sexp : Parser Error .conditional SExp :=
  fix (fun sexp_rec =>
    let plist : Parser Error .conditional SExp := gdo
      lexeme (char '(')
      let first ← sexp_rec
      let rest ← many (gdo whitespace; sexp_rec)
      lexeme (char ')')
      return listToPairs (first :: rest)
      grade_by by simp
    choice patom plist)

end SExp
