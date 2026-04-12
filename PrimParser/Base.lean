import Mathlib.Data.Vector.Basic
import Mathlib.Order.Fin.Basic

variable {α : Type}

abbrev NonEmptyList α := { l : List α // l ≠ [] }
abbrev NonEmptyList.mk (x : α) (xs : List α) : NonEmptyList α := ⟨x :: xs, by simp⟩
abbrev NonEmptyList.toList : NonEmptyList α → List α := (·.1)
infixr:67 " ::₁ " => NonEmptyList.mk
