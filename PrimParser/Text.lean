import Mathlib.Order.Fin.Basic

/-! Length-indexed input text. -/

/-- Input to a parser. `n` is the number of bytes that haven't been consumed yet. -/
structure Text (n : Nat) where
  bytes : ByteArray
  valid : n ≤ bytes.size

namespace Text

variable {n m k : Nat}

@[inline] def pos (t : Text n) : Nat := t.bytes.size - n

theorem pos_lt (t : Text (n + 1)) : t.pos < t.bytes.size := by
  have := t.valid; simp only [pos]; omega

@[inline] def head (t : Text (n + 1)) : UInt8 :=
  have := t.pos_lt
  t.bytes[t.pos]

theorem utf8Size_le
  {c : Char}
  (t : Text n)
  (h : t.bytes.utf8DecodeChar? t.pos = some c)
  : c.utf8Size ≤ n := by
  have hle := ByteArray.le_size_of_utf8DecodeChar?_eq_some h
  have hv := t.valid
  simp only [pos] at hle
  omega

def ofString (s : String) : Text s.toUTF8.size where
  bytes := s.toUTF8
  valid := by simp

def empty : Text 0 := { bytes := .empty, valid := by simp }

@[inline] def dropTo (t : Text n) (m : Nat) (h : m ≤ n) : Text m where
  bytes := t.bytes
  valid := h.trans t.valid

@[simp] theorem dropTo_self (t : Text n) (h : n ≤ n) : t.dropTo n h = t := rfl

@[simp] theorem dropTo_trans (t : Text n) (h : m ≤ n) (h' : k ≤ m)
  : (t.dropTo m h).dropTo k h' = t.dropTo k (h'.trans h) := rfl

end Text
