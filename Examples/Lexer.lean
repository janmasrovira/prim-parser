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

def one : StringParser conditional Tk :=
  oneOf (
    (Tk.num <$>ᵍ nat) ::₁
    [ Tk.plus   <$ᵍ char '+'
    , Tk.minus  <$ᵍ char '-'
    , Tk.times  <$ᵍ char '*'
    , Tk.lparen <$ᵍ char '('
    , Tk.rparen <$ᵍ char ')' ])

def lex : StringParser flexible (Array Tk) := gdo
  whitespace
  let ts ← many (lexeme one)
  return ts.toArray

def sym (t : Tk) : TokenParser Tk conditional PUnit := skipSatisfy (· == t)

def num : TokenParser Tk conditional Nat :=
  token fun
    | .num n => some n
    | _ => none

def addOp : TokenParser Tk conditional (Nat → Nat → Nat) :=
  (· + ·) <$ᵍ sym .plus <|> (· - ·) <$ᵍ sym .minus

def mulOp : TokenParser Tk conditional (Nat → Nat → Nat) :=
  (· * ·) <$ᵍ sym .times

def eval : TokenParser Tk conditional Nat :=
  fix fun self =>
    let atom := num <|> rawBracket (sym .lparen) (sym .rparen) self
    chainl1 addOp (chainl1 mulOp atom)

def evalAll : TokenParser Tk conditional Nat := gdo
  let v ← eval
  eof
  return v

def run (s : String) : Option Nat := do
  let ts ← lex.runOption s
  (evalAll.runOn (Input.ofArray ts)).toOption

end Lex
