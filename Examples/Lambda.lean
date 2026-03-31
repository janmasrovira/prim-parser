-- Untyped lambda calculus parser
import PrimParser

open Parser

inductive Term where
  | var (name : String)
  | lam (param : String) (body : Term)
  | app (fn arg : Term)
  deriving Repr, BEq

namespace Term

private def ident : Parser Error .conditional String :=
  lexeme (takeWhile1 Char.isAlpha)

def term : Parser Error .conditional Term :=
  fix (fun term_rec =>
    let atom := var <$>ᵍ ident <|> parens term_rec
    let appTerm : Parser Error .conditional Term := gdo
      let f ← atom
      let args ← many atom
      return args.foldl app f
    let lamTerm : Parser Error .conditional Term := gdo
      lexeme (char '\\')
      let x ← ident
      lexeme (char '.')
      let body ← term_rec
      return lam x body
    lamTerm <|> appTerm)

end Term
