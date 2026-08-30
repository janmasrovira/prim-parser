import PrimParser.Buffer

open Buffer

/-- Reads tokens of type `t` from a buffer `σ`.
A token `t : τ` has a width of `width t` units. -/
class Reader (σ τ : Type) [Buffer σ] where
  width : τ → Nat
  width_pos : ∀ t, 0 < width t
  /-- `remaining` is the number of unconsumed units from `σ`. -/
  nextTok : σ → (remaining : Nat) → Option τ
  nextTok_le : ∀ {s n t}, nextTok s n = some t → width t ≤ n

namespace Reader

variable {σ τ : Type} [Buffer σ] [Reader σ τ]

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

instance : Reader ByteArray Char where
  width := Char.utf8Size
  width_pos := Char.utf8Size_pos
  nextTok s n := s.utf8DecodeChar? (s.size - n)
  nextTok_le h := by
    have := ByteArray.le_size_of_utf8DecodeChar?_eq_some h
    omega

@[simp] theorem width_byteArray (c : Char) : width ByteArray c = c.utf8Size := rfl
@[simp] theorem nextTok_byteArray (b : ByteArray) (n : Nat)
  : nextTok b n = b.utf8DecodeChar? (b.size - n) := rfl

instance : Reader ByteArray UInt8 where
  width _ := 1
  width_pos _ := by simp
  nextTok b n := b[b.size - n]?
  nextTok_le h := by
    have := getElem?_eq_some_iff.mp h |>.fst
    omega

@[simp] theorem width_uint8 (t : UInt8) : width ByteArray t = 1 := rfl
@[simp] theorem nextTok_uint8 (b : ByteArray) (n : Nat)
  : nextTok b n = b[b.size - n]? := rfl

instance {τ : Type} : Reader (Array τ) τ where
  width _ := 1
  width_pos _ := by simp
  nextTok a n := a[a.size - n]?
  nextTok_le h := by
    have := Array.getElem?_eq_some_iff.mp h |>.fst
    omega

@[simp] theorem width_array {τ : Type} (t : τ) : width (Array τ) t = 1 := rfl
@[simp] theorem nextTok_array {τ : Type} (a : Array τ) (n : Nat)
  : nextTok a n = a[a.size - n]? := rfl

end Reader

open Reader

/-- This class is for documentation only. -/
class LawfulReader (σ τ : Type) [Buffer σ] [Reader σ τ] : Prop where
  nextTok_saturate : ∀ (s : σ) (n : Nat), nextTok (τ := τ) s n = nextTok s (min n (size s))

instance : LawfulReader ByteArray Char where
  nextTok_saturate _ _ := by simp; congr 1; omega

instance : LawfulReader ByteArray UInt8 where
  nextTok_saturate _ _ := by simp; congr 1; omega

instance {τ : Type} : LawfulReader (Array τ) τ where
  nextTok_saturate _ _ := by simp; congr 1; omega
