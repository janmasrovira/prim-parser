import PrimParser

open Parser Parser.Char

inductive Tk where
  | num (n : Nat)
  | plus
  | minus
  | times
  | lparen
  | rparen
  deriving Repr, BEq, Inhabited

namespace Lex

def one : StringParser Error conditional Tk :=
  oneOf (
    (Tk.num <$>ᵍ nat) ::₁
    [ Tk.plus <$ᵍ char '+'
    , Tk.minus <$ᵍ char '-'
    , Tk.times <$ᵍ char '*'
    , Tk.lparen <$ᵍ char '('
    , Tk.rparen <$ᵍ char ')' ])

def lex : StringParser Error flexible (Array Tk) := gdo
  whitespace
  let ts ← many (lexeme one)
  return ts.toArray

def sym (t : Tk) : TokenParser Tk Error conditional PUnit := skipSatisfy (· == t)

def num : TokenParser Tk Error conditional Nat :=
  token fun
    | .num n => some n
    | _ => none

def addOp : TokenParser Tk Error conditional (Nat → Nat → Nat) :=
  (· + ·) <$ᵍ sym .plus <|> (· - ·) <$ᵍ sym .minus

def mulOp : TokenParser Tk Error conditional (Nat → Nat → Nat) :=
  (· * ·) <$ᵍ sym .times

def eval : TokenParser Tk Error conditional Nat :=
  fix fun self =>
    let atom := num <|> rawBracket (sym .lparen) (sym .rparen) self
    chainl1 addOp (chainl1 mulOp atom)

def evalAll : TokenParser Tk Error conditional Nat := gdo
  let v ← eval
  eof
  return v

def run (s : String) : Option Nat := do
  let ts ← lex.runOption s
  (evalAll.runOn (Input.ofArray ts)).toOption

end Lex
