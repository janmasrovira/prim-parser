import PrimParser.Base

/-- Three-valued modality tracking whether a property holds always, possibly, or never. -/
inductive Necessity where
  | possibly
  | always
  | never
  deriving Repr

namespace Necessity

instance : Max Necessity where
  max a b := match a, b with
    | always, _ => always
    | possibly, never => possibly
    | _, _ => b

instance : Min Necessity where
  min a b := match a, b with
    | never, _ => never
    | possibly, always => possibly
    | _, _ => b

instance : LinearOrder Necessity := by
  let toFin : Necessity → Fin 3
    | never => 0
    | possibly => 1
    | always => 2
  apply LinearOrder.lift toFin
  intro x y p; cases x <;> cases y <;> cases p <;> rfl
  repeat (intro x y; cases x <;> cases y <;> rfl)

instance : BoundedOrder Necessity where
  top := always
  bot := never
  le_top a := by cases a <;> decide
  bot_le a := by cases a <;> decide

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
  one := never
  one_mul a := by cases a <;> decide
  mul_one a := by cases a <;> decide

instance : Lattice Necessity where

instance : DistribLattice Necessity where
  le_sup_inf a b c := by cases a <;> cases b <;> cases c <;> decide

/-- Flips `always` and `never`, leaving `possibly` unchanged. -/
def complement : Necessity → Necessity
  | always => never
  | possibly => possibly
  | never => always

instance : Complement Necessity where
  complement := complement

variable
  (a b : Necessity)

@[simp] theorem complement_always : always.complement = never := by decide
@[simp] theorem complement_possibly : possibly.complement = possibly := by decide
@[simp] theorem complement_never : never.complement = always := by decide
@[simp] theorem max_never_right : a ⊔ .never = a := by cases a <;> decide
@[simp] theorem max_never_left : .never ⊔ a = a := by cases a <;> decide

@[simp] theorem never_le : never ≤ a := by cases a <;> decide
@[simp] theorem le_always : a ≤ always := by cases a <;> decide
@[simp] theorem max_always : a ⊔ b = always ↔ a = always ∨ b = always := by
  cases a <;> cases b <;> decide
@[simp] theorem max_never : a ⊔ b = never ↔ a = never ∧ b = never := by
  cases a <;> cases b <;> decide
@[simp] theorem min_never : a ⊓ b = never ↔ a = never ∨ b = never := by
  cases a <;> cases b <;> decide
@[simp] theorem min_always : a ⊓ b = always ↔ a = always ∧ b = always := by
  cases a <;> cases b <;> decide
@[simp] theorem complement_always_iff : a.complement = always ↔ a = never := by
  cases a <;> decide
@[simp] theorem complement_never_iff : a.complement = never ↔ a = always := by
  cases a <;> decide

/-- Conditional selection: when `sel` is `always` returns `a`, when `never` returns `b`,
when `possibly` returns a conservative value (see theorem `ite_possibly` and `ite_possibly_cases`). -/
abbrev ite (sel a b : Necessity) : Necessity := (a ⊓ b) ⊔ sel ⊓ a ⊔ sel.complement ⊓ b
@[simp] theorem ite_always : always.ite a b = a := by simp
@[simp] theorem ite_never : never.ite a b = b := by simp
@[simp] theorem ite_possibly : possibly.ite a b = (a ⊓ b) ⊔ possibly ⊓ (a ⊔ b) := by
  cases a <;> cases b <;> simp
@[simp] theorem ite_possibly_cases :
  possibly.ite a b =
  match a, b with
  | never, never => never
  | always, always => always
  | _, _ => possibly
  := by cases a <;> cases b <;> simp
@[simp] theorem ite_idem : b.ite a a = a := by
  cases a <;> simp

end Necessity
