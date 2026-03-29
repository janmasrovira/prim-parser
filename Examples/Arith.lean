import PrimParser

open Parser

inductive Expr where
  | lit (n : Nat)
  | add (l r : Expr)
  | sub (l r : Expr)
  | mul (l r : Expr)
  | div (l r : Expr)
  deriving Repr, BEq

namespace Expr

def eval : Expr → Int
  | .lit n => n
  | .add l r => l.eval + r.eval
  | .sub l r => l.eval - r.eval
  | .mul l r => l.eval * r.eval
  | .div l r => l.eval / r.eval

private def addOp : Parser Error .conditional (Expr → Expr → Expr) :=
  choice
    ((fun _ => Expr.add) <$>ᵍ lexeme (char '+'))
    ((fun _ => Expr.sub) <$>ᵍ lexeme (char '-'))

private def mulOp : Parser Error .conditional (Expr → Expr → Expr) :=
  choice
    ((fun _ => Expr.mul) <$>ᵍ lexeme (char '*'))
    ((fun _ => Expr.div) <$>ᵍ lexeme (char '/'))

def expr : Parser Error .conditional Expr :=
  fix (fun expr_rec =>
    let atom := choice (Expr.lit <$>ᵍ lexeme nat) (parens expr_rec)
    let term := chainl1 mulOp atom
    chainl1 addOp term)

end Expr
