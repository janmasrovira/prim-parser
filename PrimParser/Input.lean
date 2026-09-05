import PrimParser.Reader

/-! Length-indexed parser input. -/

open Buffer Reader

/-- Input to a parser. `n` is the number of units that haven't been consumed yet.

NOTE: The main reason `n` is a type parameter instead of a field is performance.
Because `n` is not a field, `buf` is the only non-Prop field, so `Input` is erased during compilation.
-/
structure Input (σ : Type) [Buffer σ] (n : Nat) where
  buf : σ
  valid : n ≤ size buf

namespace Input

variable {σ τ : Type} [Buffer σ] {n m k : Nat}

abbrev nextTok [Reader σ τ] (inp : Input σ n) : Option τ := Reader.nextTok inp.buf n

theorem width_le
  {t : τ}
  [Reader σ τ]
  (inp : Input σ n)
  (h : inp.nextTok = some t)
  : width σ t ≤ n :=
  Reader.nextTok_le h

theorem sub_width_lt
  {t : τ}
  [Reader σ τ]
  {inp : Input σ n}
  (h : inp.nextTok = some t)
  : n - width σ t < n :=
  Reader.sub_width_lt h

@[simp] theorem nextTok_eq_none [Reader σ τ] {inp : Input σ 0}
  : inp.nextTok (τ := τ) = none :=
  Reader.nextTok_zero _

@[inline] def dropTo (inp : Input σ n) (m : Nat) (h : m ≤ n := by omega) : Input σ m where
  buf := inp.buf
  valid := h.trans inp.valid

@[simp] theorem dropTo_self (inp : Input σ n) (h : n ≤ n) : inp.dropTo n h = inp := rfl

@[simp] theorem dropTo_trans (inp : Input σ n) (h : m ≤ n) (h' : k ≤ m)
  : (inp.dropTo m h).dropTo k h' = inp.dropTo k (h'.trans h) := rfl

@[simp] theorem dropTo_buf (inp : Input σ n) (h : m ≤ n) : (inp.dropTo m h).buf = inp.buf := rfl

/-- how many units have been consumedfrom `inp`. -/
@[inline] def pos (inp : Input σ n) : Nat := size inp.buf - n

@[simp] theorem pos_dropTo (inp : Input σ n) (h : m ≤ n)
  : (inp.dropTo m h).pos = inp.pos + (n - m) := by
  have := inp.valid; simp only [pos, dropTo_buf]; omega

theorem pos_lt (inp : Input σ (n + 1)) : inp.pos < size inp.buf := by
  have := inp.valid; simp only [pos]; omega

/-- Move past one token. -/
abbrev advance [Reader σ τ] (inp : Input σ n) (t : τ) : Input σ (n - width σ t) :=
  inp.dropTo (n - width σ t)

/-- Skip forward while `f` holds, returning the number of units left unconsumed. -/
@[specialize] def skipWhile [Reader σ τ] (f : τ → Bool) {n : Nat} (inp : Input σ n) : {m : Nat // m ≤ n} :=
  match h : inp.nextTok (τ := τ) with
  | some t =>
    if f t then
      have := inp.width_le h
      have := width_pos (σ := σ) t
      let r := skipWhile f (inp.advance t)
      ⟨r.val, by have := r.property; omega⟩
    else ⟨n, by omega⟩
  | none => ⟨n, by omega⟩
  termination_by n

section

variable [Reader σ τ] {f : τ → Bool} {t : τ} {inp : Input σ n}

theorem skipWhile_accept
  (h : inp.nextTok = some t := by assumption)
  (hf : f t := by assumption)
  : (skipWhile f inp).val = (skipWhile f (inp.advance t)).val := by
  rw [skipWhile]; split <;> simp_all; subst_vars; rfl

theorem skipWhile_reject
  (h : inp.nextTok = some t := by assumption)
  (hf : ¬ f t := by assumption)
  : (skipWhile f inp).val = n := by
  rw [skipWhile]; split <;> simp_all

theorem skipWhile_eof
  (h : inp.nextTok (τ := τ) = none := by assumption)
  : (skipWhile f inp).val = n := by
  rw [skipWhile]; split <;> simp_all

end

/-- The scanners make progress exactly when the next token is accepted. -/
theorem skipWhile_lt_iff [Reader σ τ] {f : τ → Bool} {inp : Input σ n}
  : (skipWhile f inp).val < n ↔ ∃ t, inp.nextTok = some t ∧ f t := by
  fun_cases skipWhile f inp <;> simp_all; omega

def ofArray {τ : Type} (a : Array τ) : Input (Array τ) a.size where
  buf := a
  valid := by simp

def ofByteArray (b : ByteArray) : Input ByteArray b.size where
  buf := b
  valid := by simp

section Bytes

variable {n : Nat}

@[inline] def head (inp : Input ByteArray (n + 1)) : UInt8 :=
  have : inp.pos < inp.buf.size := by simpa using inp.pos_lt
  inp.buf[inp.pos]

def ofString (s : String) : Input ByteArray s.toUTF8.size where
  buf := s.toUTF8
  valid := by simp

/-- Collect characters while `f` holds, returning them as a `String`. -/
@[specialize] def takeWhile (f : Char → Bool) {n : Nat} (inp : Input ByteArray n) : String :=
  go inp ""
where
  @[specialize] go {m : Nat} (inp : Input ByteArray m) (acc : String) : String :=
    match h : inp.nextTok (τ := Char) with
    | some c =>
      if f c then
        have : c.utf8Size ≤ m := by simpa using inp.width_le h
        have := Char.utf8Size_pos c
        go (inp.advance c) (acc.push c)
      else acc
    | none => acc
  termination_by m

variable {f : Char → Bool} {c : Char} {inp : Input ByteArray n} {acc : String}

theorem takeWhile_go_accept
  (h : inp.nextTok = some c := by assumption)
  (hf : f c := by assumption)
  : takeWhile.go f inp acc = takeWhile.go f (inp.advance c) (acc.push c) := by
  rw [takeWhile.go]; split <;> simp_all; subst_vars; rfl

theorem takeWhile_go_reject
  (h : inp.nextTok = some c := by assumption)
  (hf : ¬ f c := by assumption)
  : takeWhile.go f inp acc = acc := by
  rw [takeWhile.go]; split <;> simp_all

theorem takeWhile_go_eof
  (h : inp.nextTok (τ := Char) = none := by assumption)
  : takeWhile.go f inp acc = acc := by
  rw [takeWhile.go]; split <;> simp_all

theorem takeWhile_reject
  (h : inp.nextTok = some c := by assumption)
  (hf : ¬ f c := by assumption)
  : takeWhile f inp = "" := by rw [takeWhile, takeWhile_go_reject]

theorem takeWhile_eof
  (h : inp.nextTok (τ := Char) = none)
  : takeWhile f inp = "" := by rw [takeWhile, takeWhile_go_eof]

private theorem utf8ByteSize_takeWhile_go
  (f : Char → Bool)
  (inp : Input ByteArray n)
  (acc : String)
  : (takeWhile.go f inp acc).utf8ByteSize + (skipWhile f inp).val = acc.utf8ByteSize + n := by
  fun_induction takeWhile.go f inp acc with
  | case1 =>
    rw [skipWhile_accept]
    simp only [String.utf8ByteSize_push, width_byteArray] at *
    omega
  | case2 => rw [skipWhile_reject]
  | case3 => rw [skipWhile_eof]

theorem utf8ByteSize_takeWhile
  (f : Char → Bool)
  (inp : Input ByteArray n)
  : (takeWhile f inp).utf8ByteSize + (skipWhile f inp).val = n := by
  simp [takeWhile, utf8ByteSize_takeWhile_go]

theorem val_skipWhile
  (f : Char → Bool)
  (inp : Input ByteArray n)
  : (skipWhile f inp).val = n - (takeWhile f inp).utf8ByteSize := by
  have := utf8ByteSize_takeWhile f inp
  omega

/-- A character the predicate accepts is part of what `takeWhile` collects. -/
theorem utf8Size_le_utf8ByteSize_takeWhile
  (h : inp.nextTok = some c := by assumption)
  (hf : f c := by assumption)
  : c.utf8Size ≤ (takeWhile f inp).utf8ByteSize := by
  have := skipWhile_accept (f := f) (t := c)
  have := skipWhile f (inp.advance c) |>.property
  have := utf8ByteSize_takeWhile f inp
  have : c.utf8Size ≤ n := by simpa using inp.width_le h
  simp only [width_byteArray] at *
  omega

theorem utf8ByteSize_takeWhile_pos_iff (f : Char → Bool) (inp : Input ByteArray n)
  : 0 < (takeWhile f inp).utf8ByteSize ↔ ∃ c, inp.nextTok = some c ∧ f c := by
  rw [← skipWhile_lt_iff]
  have := utf8ByteSize_takeWhile f inp
  omega

/-- Parse a sequence of ASCII digits as a decimal value. -/
def foldDigits {n : Nat} (inp : Input ByteArray n) : Nat × Nat :=
  go inp 0
where
  go {m : Nat} (inp : Input ByteArray m) (acc : Nat) : Nat × Nat :=
    match h : inp.nextTok (τ := Char) with
    | some c =>
      if c.isDigit then
        have : c.utf8Size <= m := by simpa using inp.width_le h
        have := Char.utf8Size_pos c
        go (inp.advance c) (acc * 10 + (c.toNat - '0'.toNat))
      else (acc, m)
    | none => (acc, m)

theorem foldDigits_go_accept
  {acc : Nat}
  (h : inp.nextTok = some c := by assumption)
  (hd : c.isDigit = true := by assumption)
  : foldDigits.go inp acc = foldDigits.go (inp.advance c) (acc * 10 + (c.toNat - '0'.toNat)) := by
  rw [foldDigits.go]; grind

theorem foldDigits_go_le
  (inp : Input ByteArray n)
  (acc : Nat)
  : (foldDigits.go inp acc).2 <= n := by
  fun_induction foldDigits.go inp acc <;> grind

theorem foldDigits_lt_iff
  (inp : Input ByteArray n)
  : (foldDigits inp).2 < n ↔ ∃ c : Char, inp.nextTok = some c ∧ c.isDigit = true := by
  rw [foldDigits]
  fun_cases foldDigits.go inp 0 <;> grind [foldDigits_go_le, Input.sub_width_lt]

end Bytes

end Input
