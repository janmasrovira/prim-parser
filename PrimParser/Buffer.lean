import Mathlib.Order.Fin.Basic

/-- `σ` is a sequence of tokens of type `τ`.
The total size of the buffer is `size`, measured in (abstract) units.
A token `t : τ` has a width of `width t` units. -/
class Buffer (σ τ : Type) where
  size : σ → Nat
  nil : σ
  width : τ → Nat
  width_pos : ∀ t, 0 < width t
  /-- `remaining` is the number of unconsumed units from `σ`. -/
  nextTok : σ → (remaining : Nat) → Option τ
  nextTok_le : ∀ {s n t}, nextTok s n = some t → width t ≤ n

namespace Buffer

variable {σ τ : Type} [Buffer σ τ]

@[simp] theorem nextTok_zero (s : σ) : nextTok (τ := τ) s 0 = none := by
  cases h : nextTok (τ := τ) s 0 with
  | none => rfl
  | some t => have := nextTok_le h; have := width_pos (σ := σ) t; omega

theorem sub_width_lt {s : σ} {n : Nat} {t : τ}
  (h : nextTok s n = some t)
  : n - width σ t < n := by
  have := nextTok_le h
  have := width_pos (σ := σ) t
  omega

instance : Buffer ByteArray Char where
  size := ByteArray.size
  nil := .empty
  width := Char.utf8Size
  width_pos := Char.utf8Size_pos
  nextTok s n := s.utf8DecodeChar? (s.size - n)
  nextTok_le h := by
    have := ByteArray.le_size_of_utf8DecodeChar?_eq_some h
    omega

@[simp] theorem size_byteArray (b : ByteArray) : size Char b = b.size := rfl
@[simp] theorem width_byteArray (c : Char) : width ByteArray c = c.utf8Size := rfl
@[simp] theorem nextTok_byteArray (b : ByteArray) (n : Nat)
  : nextTok (τ := Char) b n = b.utf8DecodeChar? (b.size - n) := rfl

instance {τ : Type} : Buffer (Array τ) τ where
  size := Array.size
  nil := #[]
  width _ := 1
  width_pos _ := by simp
  nextTok a n := a[a.size - n]?
  nextTok_le h := by
    have := Array.getElem?_eq_some_iff.mp h |>.fst
    omega

@[simp] theorem size_array {τ : Type} (a : Array τ) : size τ a = a.size := rfl
@[simp] theorem width_array {τ : Type} (t : τ) : width (Array τ) t = 1 := rfl
@[simp] theorem nextTok_array {τ : Type} (a : Array τ) (n : Nat)
  : nextTok a n = a[a.size - n]? := rfl

end Buffer

open Buffer

/-- This class is for documentation only. -/
class LawfulBuffer (σ τ : Type) [Buffer σ τ] : Prop where
  size_nil : size τ (nil τ : σ) = 0
  nextTok_saturate : ∀ (s : σ) (n : Nat), nextTok (τ := τ) s n = nextTok s (min n (size τ s))

theorem LawfulBuffer.nextTok_nil {σ τ : Type} [Buffer σ τ] [LawfulBuffer σ τ] (n : Nat)
  : nextTok (τ := τ) (nil τ : σ) n = none := by
  rw [nextTok_saturate, size_nil, Nat.min_zero, nextTok_zero]

instance : LawfulBuffer ByteArray Char where
  size_nil := rfl
  nextTok_saturate _ _ := by simp; congr 1; omega

instance {τ : Type} : LawfulBuffer (Array τ) τ where
  size_nil := rfl
  nextTok_saturate _ _ := by simp; congr 1; omega

class UnitBuffer (σ τ : Type) [Buffer σ τ] : Prop where
  width_eq_one : ∀ t : τ, width σ t = 1
  nextTok_isSome : ∀ (s : σ) (n : Nat), 0 < n → n ≤ size τ s → (nextTok (τ := τ) s n).isSome

instance {τ : Type} : UnitBuffer (Array τ) τ where
  width_eq_one _ := rfl
  nextTok_isSome _ _ _ _ := by simp_all; omega
