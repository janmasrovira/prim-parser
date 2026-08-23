import PrimParser

open Parser Parser.Utf8

inductive SExp where
  | atom (str : String)
  | pair (l r : SExp)
  deriving Repr, BEq

namespace SExp

private def listToPairs : List SExp → SExp
  | [x] => x
  | x :: xs => .pair x (listToPairs xs)
  | [] => .atom ""

def patom : Utf8Parser Error conditional SExp :=
  .atom <$>ᵍ takeWhile1 (·.isAlphanum)

def sexp : Utf8Parser Error conditional SExp :=
  fix (fun sexp_rec =>
    let plist : Utf8Parser Error conditional SExp := gdo
      lexeme lparen
      let first ← sexp_rec
      let rest ← many (gdo whitespace; sexp_rec)
      lexeme rparen
      return listToPairs (first :: rest)
    patom <|> plist)

end SExp
