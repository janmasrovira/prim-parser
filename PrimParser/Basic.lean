import Mathlib.Data.Vector.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Fin.Basic

abbrev Error := String
abbrev Text (n : Nat) := List.Vector Char n

inductive IsConsuming where
  | possibly
  | always

instance : Max IsConsuming where
  max a b := match a with
    | .always => .always
    | .possibly => b

instance : Min IsConsuming where
  min a b := match a with
    | .possibly => .possibly
    | .always => b

instance : LinearOrder IsConsuming := by
  let toFin : IsConsuming → Fin 2
    | .possibly => 0
    | .always => 1
  apply LinearOrder.lift toFin
  intro x y p; cases x <;> cases y <;> cases p <;> rfl
  repeat (intro x y; cases x <;> cases y <;> rfl)

instance : SemilatticeSup IsConsuming where
  sup := max
  sup_le a b c := by cases a <;> cases b <;> cases c <;> decide
  le_sup_left a b := by cases a <;> cases b <;> decide
  le_sup_right a b := by cases a <;> cases b <;> decide

instance : Monoid IsConsuming where
  mul := max
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> decide
  one := .possibly
  one_mul a := by cases a <;> decide
  mul_one a := by cases a <;> decide

abbrev consumptionObligation (n m : Nat) : IsConsuming → Prop
  | .always => n < m
  | .possibly => n ≤ m

structure OkResult (n : Nat) (c : IsConsuming) (α : Type) where
  result : α
  restSize : Nat
  proof : consumptionObligation restSize n c
  restText : Text restSize

abbrev Parser (ε : Type) (c : IsConsuming) (α : Type) :=
  ∀ {n}, Text n → ε ⊕ OkResult n c α

variable
  {α ε : Type}

def Error.eof : Error := "eof"
def Error.fail : Error := "fail"

def token (f : Char → Option α) : Parser Error .always α := fun {n} t =>
  match n, t with
  | 0, .nil => .inl .eof
  | Nat.succ n, ⟨c :: cs, _⟩ => match f c with
   | .some r => .inr ⟨r, n, Nat.lt_add_one n, cs, by grind⟩
   | .none => .inl .fail

def many (p : Parser ε .always α) : Parser Empty .possibly (List α) := fun {n} t =>
  match p t with
  | .inl _ => .inr ⟨[], n, by omega, t⟩
  | .inr ⟨a, n', p', t'⟩ => match many p t' with
    | .inl e => nomatch e
    | .inr ⟨as, n'', p'', t''⟩ => .inr ⟨a :: as, n'', by omega, t''⟩

inductive Many1Zero where
  | mk

def many1 (p : Parser ε .always α) : Parser Many1Zero .always (List α) := fun {n} t =>
  match p t with
  | .inl _ => .inl .mk
  | .inr ⟨a, n', p', t'⟩ =>
    match many p t' with
    | .inl e => nomatch e
    | .inr ⟨as, n'', p'', t''⟩ => .inr ⟨a :: as, n'', by omega, t''⟩

def digit : Parser Error .always (Fin 10) :=
  let f (c : Char) : Option (Fin 10) :=
    if h : '0'.toNat ≤ c.toNat && c.toNat ≤ '9'.toNat
    then .some ⟨c.toNat - '0'.toNat, by grind⟩
    else .none
  token f

def natural : Parser Error .always Nat := fun t =>
  let f (l : List (Fin 10)) : Nat := l.foldl (fun ⟨fac, acc⟩ ⟨d, _⟩
    => ⟨fac * 10, acc + fac * d⟩) ((1 : Nat), (0 : Nat)) |>.2
  match many1 digit t with
  | .inl .mk => .inl "failed to parse Nat"
  | .inr ⟨l, x1, x2, x3⟩ => .inr ⟨f l.reverse, x1, x2, x3⟩

def runParser {c} (txt : String) (p : Parser ε c α) : ε ⊕ α :=
  let l : List Char := txt.toList
  let v : List.Vector Char l.length := List.Vector.ofFn (fun ix => l.get ix)
  match p v with
  | .inl e => .inl e
  | .inr r => .inr r.result
