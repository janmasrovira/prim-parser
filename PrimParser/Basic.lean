import PrimParser.Base
import PrimParser.Necessity
import PrimParser.GradedMonad

abbrev Error := String
abbrev Text (n : Nat) := List.Vector Char n

structure Grade where
  errors : Necessity
  consumes : Necessity

namespace Grade

abbrev unconditional : Grade where
  consumes := .always
  errors := .never

abbrev conditional : Grade where
  consumes := .always
  errors := .possibly

abbrev sink : Grade where
  consumes := .always
  errors := .always

abbrev flexible : Grade where
  consumes := .possibly
  errors := .never

abbrev fallible : Grade where
  consumes := .possibly
  errors := .possibly

abbrev failing : Grade where
  consumes := .possibly
  errors := .always

abbrev pure : Grade where
  consumes := .never
  errors := .never

abbrev lookahead : Grade where
  consumes := .never
  errors := .possibly

abbrev brake : Grade where
  consumes := .never
  errors := .always

instance : Monoid Grade where
  mul a b := ⟨a.errors ⊔ b.errors, a.consumes ⊔ b.consumes⟩
  mul_assoc a b c := by cases a; cases b; simp [HMul.hMul, Mul.mul]; grind
  one := pure
  one_mul a := by cases a; simp [HMul.hMul, Mul.mul, OfNat.ofNat, pure]
  mul_one a := by cases a; simp [HMul.hMul, Mul.mul, OfNat.ofNat, pure]

end Grade

namespace Parser

abbrev consumptionWitness (n m : Nat) : Necessity → Prop
  | .always => n < m
  | .possibly => n ≤ m
  | .never => n = m

structure Result (n : Nat) (consumes : Necessity) (α : Type) where
  result : α
  restSize : Nat
  witness : consumptionWitness restSize n consumes
  restText : Text restSize

abbrev Outcome (ε : Type) (n : Nat) (g : Grade) (α : Type) : Type :=
  match g.errors with
  | .never => Result n g.consumes α
  | .possibly => ε ⊕ Result n g.consumes α
  | .always => ε

end Parser

structure Parser (ε : Type) (g : Grade) (α : Type) where
  run : ∀ {n}, Text n → Parser.Outcome ε n g α

namespace Parser

variable
  {α β ε : Type}
  {g g' : Grade}
  {ge : Necessity}

instance {n c} : Functor (Result n c) where
  map f x := {x with result := f x.result}

instance {n} : GFunctor (Result n) where
  gmap := Functor.map

instance {n} : Functor (Outcome ε n g) where
  map f x := match g with
    | ⟨e, _⟩ => match e with
     | .never => by dsimp! at x ⊢; exact f <$> x
     | .possibly => by dsimp! at x ⊢; exact (Functor.map f) <$> x
     | .always => x

def Error.eof : Error := "eof"
def Error.fail : Error := "fail"

-- TODO perhaps a generic instance of G{Functor,Applicative,Monad} for the →
-- type is possible
def Result.ap {α β : Type} {n : Nat} {ic jc : Necessity}
    (r1 : Result n ic (α → β)) (r2 : Result r1.restSize jc α)
    : Result n (ic ⊔ jc) β where
  result := r1.result r2.result
  restSize := r2.restSize
  restText := r2.restText
  witness := by
    have w1 := r1.witness
    have w2 := r2.witness
    cases ic <;> cases jc <;> simp_all [consumptionWitness] <;> omega

def Result.ap' {α β : Type} {n : Nat} {ic jc : Necessity}
    (r1 : Result n ic α) (r2 : Result r1.restSize jc (α → β))
    : Result n (ic ⊔ jc) β where
  result := r2.result r1.result
  restSize := r2.restSize
  restText := r2.restText
  witness := by
    have w1 := r1.witness
    have w2 := r2.witness
    cases ic <;> cases jc <;> simp_all [consumptionWitness] <;> omega

def Result.seq {α β : Type} {n : Nat} {ic jc : Necessity}
    (r1 : Result n ic α) (r2 : Result r1.restSize jc β)
    : Result n (ic * jc) β where
  result := r2.result
  restSize := r2.restSize
  restText := r2.restText
  witness := by
    have w1 := r1.witness
    have w2 := r2.witness
    cases ic <;> cases jc <;> simp_all [consumptionWitness] <;> omega

def Result.bindParser {α β ε : Type} {n : Nat} {xc fe fc : Necessity}
    (x : Result n xc α) (f : α → Parser ε ⟨fe, fc⟩ β)
    : Outcome ε n ⟨fe, xc * fc⟩ β :=
  match fe with
  | .always => (f x.result).run x.restText
  | .never => x.seq ((f x.result).run x.restText)
  | .possibly => match (f x.result).run x.restText with
    | .inr y => .inr (x.seq y)
    | .inl e => .inl e

instance : GFunctor (Parser ε) where
  gmap f p := ⟨fun t => f <$> p.run t⟩

def Outcome.throw {n} (e : ε) (i : .possibly ≤ g.errors := by simp) : Outcome ε n g α := by
  rcases g with ⟨g1, g2⟩
  match h : g1 with
  | .possibly => exact .inl e
  | .always => exact e
  | .never => contradiction

def bind (m : Parser ε g α) (f : α → Parser ε g' β) : Parser ε (g * g') β :=
  ⟨fun t => by
  rcases g with ⟨ge, gc⟩; rcases g' with ⟨ge', gc'⟩
  have x := m.run t
  exact match ge with
  | .always => x
  | .never => x.bindParser f
  | .possibly => match x with
    | .inl e => Outcome.throw (g := ⟨max .possibly _, _⟩) e
    | .inr x' => match ge' with
      | .always => x'.bindParser f
      | .never => .inr (x'.bindParser f)
      | .possibly => x'.bindParser f⟩

instance : GApplicative (Parser ε) where
  gpure a := ⟨fun t => Result.mk a _ rfl t⟩
  gseq f g := bind f fun f' => ⟨fun t => f' <$> (g ()).run t⟩

instance : GMonad (Parser ε) where
  gbind := bind

namespace Combinator

def char : Parser Error .conditional Char := ⟨fun {n} t =>
  match n, t with
  | 0, .nil => .inl Error.eof
  | Nat.succ n, ⟨c :: cs, _⟩ =>
   .inr ⟨c, n, Nat.lt_add_one n, cs, by grind⟩⟩

def throw (e : ε) (c : .possibly ≤ g.errors := by simp) : Parser ε g α :=
  ⟨fun _ => Outcome.throw (i := c) e⟩

def ret (a : α) (c : ge ≤ .possibly := by simp) : Parser ε ⟨ge, .never⟩ α :=
  by
  constructor
  intro n t
  cases ge <;> (simp [Outcome]; try contradiction)
  · right; exact {result := a
                  restSize := n
                  restText := t
                  witness := rfl}
  · exact {result := a
           restSize := n
           restText := t
           witness := rfl}

def token (f : Char → Option α) : Parser Error .conditional α := gdo
  let c ← char
  match f c with
  | .some r => ret r (ge := .possibly)
  | .none => throw Error.fail

end Combinator

end Parser
