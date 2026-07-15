import PrimParser.Base

/-!
# `Necessity`: a three-valued Kleene modality

Three-valued modality tracking whether a property holds `always`, `possibly`, or
`never`.

`Necessity` is the three-element Kleene chain `never < possibly < always`, and
`neg` (written `~a`) is the order-reversing involution that fixes `possibly`. That
makes `(Necessity, ⊔, ⊓, ~)` a **Kleene algebra** (De Morgan algebra + Kleene
condition), *not* a Boolean algebra: the complement law `a ⊓ ~a = ⊥` fails at
`possibly`. Hence the operation is named `neg`, not `complement`.
-/

/-- Three-valued modality tracking whether a property holds always, possibly, or never. -/
inductive Necessity where
  | possibly
  | always
  | never
  deriving Repr

export Necessity (possibly always never)

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
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one := never
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl

instance : Lattice Necessity where

instance : DistribLattice Necessity where
  le_sup_inf a b c := by cases a <;> cases b <;> cases c <;> decide

/-- Kleene negation: flips `always` and `never`, leaving `possibly` unchanged.
Written `~a`. -/
abbrev neg : Necessity → Necessity
  | always => never
  | possibly => possibly
  | never => always

@[inherit_doc] prefix:max "~" => Necessity.neg

variable
  (a b : Necessity)

/-- `~always = never`. -/
@[simp] theorem neg_always : ~always = never := rfl
/-- `~possibly = possibly` — `possibly` is the fixed point. -/
@[simp] theorem neg_possibly : ~possibly = possibly := rfl
/-- `~never = always`. -/
@[simp] theorem neg_never : ~never = always := rfl

/-- `never` is a right unit for `⊔`. -/
@[simp] theorem max_never_right : a ⊔ never = a := by cases a <;> rfl
/-- `never` is a left unit for `⊔`. -/
@[simp] theorem max_never_left : never ⊔ a = a := by cases a <;> rfl
/-- `⊔` is idempotent. -/
@[simp] theorem max_idem : a ⊔ a = a := by cases a <;> rfl

/-- `never` is the bottom element. -/
@[simp] theorem never_le : never ≤ a := bot_le
/-- `always` is the top element. -/
@[simp] theorem le_always : a ≤ always := le_top
/-- A join is `always` iff one side already is. -/
@[simp] theorem max_always : a ⊔ b = always ↔ a = always ∨ b = always := by
  cases a <;> cases b <;> decide
/-- A join is `never` iff both sides are. -/
@[simp] theorem max_never : a ⊔ b = never ↔ a = never ∧ b = never := by
  cases a <;> cases b <;> decide
/-- A meet is `never` iff one side already is. -/
@[simp] theorem min_never : a ⊓ b = never ↔ a = never ∨ b = never := by
  cases a <;> cases b <;> decide
/-- A meet is `always` iff both sides are. -/
@[simp] theorem min_always : a ⊓ b = always ↔ a = always ∧ b = always := by
  cases a <;> cases b <;> decide
/-- `~a = always` exactly when `a = never`. -/
@[simp] theorem neg_always_iff : ~a = always ↔ a = never := by
  cases a <;> decide
/-- `~a = never` exactly when `a = always`. -/
@[simp] theorem neg_never_iff : ~a = never ↔ a = always := by
  cases a <;> decide

/-! ### `neg` is a Kleene negation, not a Boolean complement -/

/-- `neg` is involutive. -/
@[simp] theorem neg_neg (a : Necessity) : ~~a = a := by
  cases a <;> rfl

/-- `neg` is order-reversing (antitone). -/
theorem neg_antitone (a b : Necessity) : a ≤ b → ~b ≤ ~a := by
  cases a <;> cases b <;> decide

/-- De Morgan law for `⊔`. -/
theorem neg_sup (a b : Necessity) : ~(a ⊔ b) = ~a ⊓ ~b := by
  cases a <;> cases b <;> rfl

/-- De Morgan law for `⊓`. -/
theorem neg_inf (a b : Necessity) : ~(a ⊓ b) = ~a ⊔ ~b := by
  cases a <;> cases b <;> rfl

/-- Kleene's condition `a ⊓ ~a ≤ b ⊔ ~b`. With the De Morgan laws above this
makes `Necessity` a Kleene algebra — strictly weaker than a Boolean algebra. -/
theorem inf_neg_le_sup_neg (a b : Necessity) :
    a ⊓ ~a ≤ b ⊔ ~b := by
  cases a <;> cases b <;> decide

/-- The Boolean complement law FAILS: `possibly ⊓ ~possibly = possibly ≠ never`.
Hence `neg` is a Kleene/De Morgan negation, not a lattice complement. -/
theorem not_boolean_complement : ∃ a : Necessity, a ⊓ ~a ≠ (⊥ : Necessity) :=
  ⟨possibly, by decide⟩

/-- Conditional selection: when `sel` is `always` returns `a`, when `never` returns `b`,
when `possibly` returns a conservative value (see theorem `ite_possibly` and `ite_possibly_cases`). -/
abbrev ite (sel a b : Necessity) : Necessity := (a ⊓ b) ⊔ sel ⊓ a ⊔ ~sel ⊓ b
/-- Selecting on `always` yields the first branch. -/
@[simp] theorem ite_always : always.ite a b = a := by simp
/-- Selecting on `never` yields the second branch. -/
@[simp] theorem ite_never : never.ite a b = b := by simp
/-- Selecting on `possibly` yields the conservative meet/join blend. -/
@[simp] theorem ite_possibly : possibly.ite a b = (a ⊓ b) ⊔ possibly ⊓ (a ⊔ b) := by
  cases a <;> cases b <;> simp
/-- On `possibly`, selection is the common branch when they agree, else `possibly`. -/
@[simp] theorem ite_possibly_cases :
  possibly.ite a b = if a = b then a else possibly
  := by cases a <;> cases b <;> simp
/-- Selection with equal branches is that branch, whatever the selector. -/
@[simp] theorem ite_idem : b.ite a a = a := by
  cases a <;> simp

end Necessity
