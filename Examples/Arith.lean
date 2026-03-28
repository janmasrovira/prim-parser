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

private def lchar (c : Char) : Parser Error .conditional PUnit :=
  lexeme (char c)

private def addOp : Parser Error .conditional (Expr → Expr → Expr) :=
  choice
    ((fun _ => Expr.add) <$>ᵍ lchar '+')
    ((fun _ => Expr.sub) <$>ᵍ lchar '-')

private def mulOp : Parser Error .conditional (Expr → Expr → Expr) :=
  choice
    ((fun _ => Expr.mul) <$>ᵍ lchar '*')
    ((fun _ => Expr.div) <$>ᵍ lchar '/')

def expr : Parser Error .conditional Expr :=
  fix (fun expr_rec =>
    let parens : Parser Error .conditional Expr := gdo
      lchar '('
      let e ← expr_rec
      lchar ')'
      return e
      grade_by by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one]
    let atom := choice (Expr.lit <$>ᵍ lexeme nat) parens
    let term := chainl1 atom mulOp
    chainl1 term addOp)

end Expr
