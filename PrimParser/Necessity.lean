import PrimParser.Base

inductive Necessity where
  | possibly
  | always
  | never

instance : Max Necessity where
  max a b := match a, b with
    | .always, _ => .always
    | .possibly, .never => .possibly
    | _, _ => b

instance : Min Necessity where
  min a b := match a, b with
    | .never, _ => .never
    | .possibly, .always => .possibly
    | _, _ => b

instance : LinearOrder Necessity := by
  let toFin : Necessity → Fin 3
    | .never => 0
    | .possibly => 1
    | .always => 2
  apply LinearOrder.lift toFin
  intro x y p; cases x <;> cases y <;> cases p <;> rfl
  repeat (intro x y; cases x <;> cases y <;> rfl)

instance : SemilatticeSup Necessity where
  sup := max
  sup_le a b c := by cases a <;> cases b <;> cases c <;> decide
  le_sup_left a b := by cases a <;> cases b <;> decide
  le_sup_right a b := by cases a <;> cases b <;> decide

instance : SemilatticeInf Necessity where
  inf := min
  le_inf a b c := by cases a <;> cases b <;> cases c <;> decide
  inf_le_left a b := by cases a <;> cases b <;> decide
  inf_le_right a b := by cases a <;> cases b <;> decide

instance : Monoid Necessity where
  mul := max
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> decide
  one := .never
  one_mul a := by cases a <;> decide
  mul_one a := by cases a <;> decide
