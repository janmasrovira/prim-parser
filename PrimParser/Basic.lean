import PrimParser.Base
import PrimParser.Necessity
import IMonad.Graded

abbrev Error := String
abbrev Text (n : Nat) := List.Vector Char n

structure Grade where
  errors : Necessity
  consumes : Necessity

namespace Grade

def unconditional : Grade where
  consumes := .always
  errors := .never

def conditional : Grade where
  consumes := .always
  errors := .possibly

def sink : Grade where
  consumes := .always
  errors := .always

def flexible : Grade where
  consumes := .possibly
  errors := .never

def fallible : Grade where
  consumes := .possibly
  errors := .possibly

def failing : Grade where
  consumes := .possibly
  errors := .always

def pure : Grade where
  consumes := .never
  errors := .never

def lookahead : Grade where
  consumes := .never
  errors := .possibly

def brake : Grade where
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

abbrev Parser (ε : Type) (g : Grade) (α : Type) :=
  ∀ {n}, Text n → Parser.Outcome ε n g α

namespace Parser

variable
  {α ε : Type}
  {g : Grade}
  [Inhabited ε]

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

def token (f : Char → Option α) : Parser Error .conditional α := fun {n} t =>
  match n, t with
  | 0, .nil => .inl Error.eof
  | Nat.succ n, ⟨c :: cs, _⟩ => match f c with
   | .some r => .inr ⟨r, n, Nat.lt_add_one n, cs, by grind⟩
   | .none => .inl Error.fail

-- TODO perhaps a generic instance of G{Functor,Applicative,Monad} for the →
-- type is possible
def Result.seq {α β : Type} {n : Nat} {ic jc : Necessity}
    (r1 : Result n ic (α → β)) (r2 : Result r1.restSize jc α)
    : Result n (ic ⊔ jc) β where
  result := r1.result r2.result
  restSize := r2.restSize
  restText := r2.restText
  witness := by
    have w1 := r1.witness
    have w2 := r2.witness
    cases ic <;> cases jc <;> simp_all [consumptionWitness] <;> omega

instance : GFunctor (Parser ε) where
  gmap f p _ t := f <$> p t

instance : GApplicative (Parser ε) where
  gpure a _ t := ⟨a, _, rfl, t⟩
  gseq f g _n t := by
    expose_names
    specialize f t
    rcases i with ⟨ie, ic⟩; rcases j with ⟨je, jc⟩
    cases ie <;> simp [Outcome, HMul.hMul, Mul.mul] at ⊢ f
    case always => exact f
    case possibly =>
      cases je <;> simp at ⊢
      case always =>
        rcases f with e | r
        · exact e
        · exact g () r.restText
      case possibly =>
        rcases f with e | r
        · exact .inl e
        · rcases g () r.restText with e | r2
          · exact .inl e
          · exact .inr (r.seq r2)
      case never =>
        rcases f with e | r
        · exact .inl e
        · exact .inr (r.seq (g () r.restText))
    case never =>
      specialize g () f.restText
      cases je <;> simp [Outcome] at g ⊢
      case always => exact g
      case possibly =>
        rcases g with e | r
        · exact .inl e
        · exact .inr (f.seq r)
      case never => exact f.seq g


end Parser
