import PrimParser

open Parser Parser.Utf8

inductive Token where
  | num (n : Nat)
  | plus
  | minus
  | times
  | lparen
  | rparen
  deriving Repr, BEq

namespace Lex

def tok : Utf8Parser Error conditional Token :=
  oneOf (
    (Token.num <$>ᵍ nat) ::₁
    [ char '+' $>ᵍ Token.plus
    , char '-' $>ᵍ Token.minus
    , char '*' $>ᵍ Token.times
    , char '(' $>ᵍ Token.lparen
    , char ')' $>ᵍ Token.rparen ])

def lex : Utf8Parser Error flexible (Array Token) := gdo
  whitespace
  let ts ← many (lexeme tok)
  return ts.toArray

def sym (t : Token) : TokenParser Token Error conditional PUnit := skipSatisfy (· == t)

def num : TokenParser Token Error conditional Nat :=
  token fun
    | .num n => some n
    | _ => none

def addOp : TokenParser Token Error conditional (Nat → Nat → Nat) :=
  (gdo sym .plus; return (· + ·))
  <|> (gdo sym .minus; return (· - ·))

def mulOp : TokenParser Token Error conditional (Nat → Nat → Nat) :=
  gdo sym .times; return (· * ·)

def eval : TokenParser Token Error conditional Nat :=
  fix fun self =>
    let atom := num <|> rawBracket (sym .lparen) (sym .rparen) self
    chainl1 addOp (chainl1 mulOp atom)

def evalAll : TokenParser Token Error conditional Nat := gdo
  let v ← eval
  eof
  return v

def run (s : String) : Option Nat := do
  let ts ← lex.runOption s
  (evalAll.runOn (Input.ofArray ts)).toOption

end Lex
