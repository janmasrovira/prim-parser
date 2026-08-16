import Mathlib.Order.Fin.Basic

/-! Length-indexed parser input. -/

/-- Input to a parser. `n` is the number of bytes that haven't been consumed yet. -/
structure Input (n : Nat) where
  bytes : ByteArray
  valid : n ≤ bytes.size

namespace Input

variable {n m k : Nat}

@[inline] def pos (t : Input n) : Nat := t.bytes.size - n

theorem pos_lt (t : Input (n + 1)) : t.pos < t.bytes.size := by
  have := t.valid; simp only [pos]; omega

@[inline] def head (t : Input (n + 1)) : UInt8 :=
  have := t.pos_lt
  t.bytes[t.pos]

abbrev nextChar (t : Input n) : Option Char := t.bytes.utf8DecodeChar? t.pos

theorem utf8Size_le
  {c : Char}
  (t : Input n)
  (h : t.nextChar = some c)
  : c.utf8Size ≤ n := by
  have hle := ByteArray.le_size_of_utf8DecodeChar?_eq_some h
  have hv := t.valid
  simp only [pos] at hle
  omega

theorem sub_utf8Size_lt
  {c : Char}
  {t : Input n}
  (h : t.nextChar = some c)
  : n - c.utf8Size < n := by
  have := utf8Size_le t h
  have := Char.utf8Size_pos c
  omega

theorem nextChar_eq_none {t : Input 0} : t.nextChar = none := by
  cases h : t.nextChar with
  | none => rfl
  | some c => have := t.utf8Size_le h; have := Char.utf8Size_pos c; omega

def ofString (s : String) : Input s.toUTF8.size where
  bytes := s.toUTF8
  valid := by simp

def empty : Input 0 := { bytes := .empty, valid := by simp }

@[inline] def dropTo (t : Input n) (m : Nat) (h : m ≤ n := by omega) : Input m where
  bytes := t.bytes
  valid := h.trans t.valid

@[simp] theorem dropTo_self (t : Input n) (h : n ≤ n) : t.dropTo n h = t := rfl

@[simp] theorem dropTo_trans (t : Input n) (h : m ≤ n) (h' : k ≤ m)
  : (t.dropTo m h).dropTo k h' = t.dropTo k (h'.trans h) := rfl

/-- Move `c.utf8Size` ahead -/
abbrev advance (t : Input n) (c : Char) : Input (n - c.utf8Size) := t.dropTo (n - c.utf8Size)

/-- Skip forward while `f` holds, returning the number of bytes left unconsumed. -/
@[specialize] def skipWhile (f : Char → Bool) {n : Nat} (t : Input n) : {m : Nat // m ≤ n} :=
  match h : t.nextChar with
  | some c =>
    if f c then
      have := t.utf8Size_le h
      have := Char.utf8Size_pos c
      let r := skipWhile f (t.advance c)
      ⟨r.val, by have := r.property; omega⟩
    else ⟨n, by omega⟩
  | none => ⟨n, by omega⟩

section

variable {f : Char → Bool} {c : Char} {t : Input n}

theorem skipWhile_accept
  (h : t.nextChar = some c := by assumption)
  (hf : f c := by assumption)
  : (skipWhile f t).val = (skipWhile f (t.advance c)).val := by
  rw [skipWhile]; split <;> simp_all; subst_vars; rfl

theorem skipWhile_reject
  (h : t.nextChar = some c := by assumption)
  (hf : ¬ f c := by assumption)
  : (skipWhile f t).val = n := by
  rw [skipWhile]; split <;> simp_all

theorem skipWhile_eof
  (h : t.nextChar = none := by assumption)
  : (skipWhile f t).val = n := by
  rw [skipWhile]; split <;> simp_all

end

/-- Collect characters while `f` holds, returning them as a `String`. -/
@[specialize] def takeWhile (f : Char → Bool) {n : Nat} (t : Input n) : String :=
  go t ""
where
  @[specialize] go {m : Nat} (t : Input m) (acc : String) : String :=
    match h : t.nextChar with
    | some c =>
      if f c then
        have := t.utf8Size_le h
        have := Char.utf8Size_pos c
        go (t.advance c) (acc.push c)
      else acc
    | none => acc

section

variable {f : Char → Bool} {c : Char} {t : Input n} {acc : String}

theorem takeWhile_go_accept
  (h : t.nextChar = some c := by assumption)
  (hf : f c := by assumption)
  : takeWhile.go f t acc = takeWhile.go f (t.advance c) (acc.push c) := by
  rw [takeWhile.go]; split <;> simp_all; subst_vars; rfl

theorem takeWhile_go_reject
  (h : t.nextChar = some c := by assumption)
  (hf : ¬ f c := by assumption)
  : takeWhile.go f t acc = acc := by
  rw [takeWhile.go]; split <;> simp_all

theorem takeWhile_go_eof
  (h : t.nextChar = none := by assumption)
  : takeWhile.go f t acc = acc := by
  rw [takeWhile.go]; split <;> simp_all

theorem takeWhile_reject
  (h : t.nextChar = some c := by assumption)
  (hf : ¬ f c := by assumption)
  : takeWhile f t = "" := by rw [takeWhile, takeWhile_go_reject]

theorem takeWhile_eof
  (h : t.nextChar = none)
  : takeWhile f t = "" := by rw [takeWhile, takeWhile_go_eof]

private theorem utf8ByteSize_takeWhile_go
  (f : Char → Bool)
  (t : Input n)
  (acc : String)
  : (takeWhile.go f t acc).utf8ByteSize + (skipWhile f t).val = acc.utf8ByteSize + n := by
  fun_induction takeWhile.go f t acc with
  | case1 =>
    rw [skipWhile_accept]
    simp only [String.utf8ByteSize_push] at *
    omega
  | case2 => rw [skipWhile_reject]
  | case3 => rw [skipWhile_eof]

theorem utf8ByteSize_takeWhile
  (f : Char → Bool)
  (t : Input n)
  : (takeWhile f t).utf8ByteSize + (skipWhile f t).val = n := by
  simp [takeWhile, utf8ByteSize_takeWhile_go]

theorem val_skipWhile
  (f : Char → Bool)
  (t : Input n)
  : (skipWhile f t).val = n - (takeWhile f t).utf8ByteSize := by
  have := utf8ByteSize_takeWhile f t
  omega

/-- A character the predicate accepts is part of what `takeWhile` collects. -/
theorem utf8Size_le_utf8ByteSize_takeWhile
  (h : t.nextChar = some c := by assumption)
  (hf : f c := by assumption)
  : c.utf8Size ≤ (takeWhile f t).utf8ByteSize := by
  have := skipWhile_accept
  have := skipWhile f (t.advance c) |>.property
  have := utf8ByteSize_takeWhile f t
  have := t.utf8Size_le h
  omega

/-- The scanners make progress exactly when the next character is accepted. -/
theorem skipWhile_lt_iff {f : Char → Bool} {t : Input n}
  : (skipWhile f t).val < n ↔ ∃ c, t.nextChar = some c ∧ f c := by
  fun_cases skipWhile f t <;> simp_all; omega

theorem utf8ByteSize_takeWhile_pos_iff (f : Char → Bool) (t : Input n)
  : 0 < (takeWhile f t).utf8ByteSize ↔ ∃ c, t.nextChar = some c ∧ f c := by
  rw [← skipWhile_lt_iff]
  have := utf8ByteSize_takeWhile f t
  omega

end

end Input
