import PrimParser.Buffer

/-! Length-indexed parser input. -/

open Buffer

/-- Input to a parser. `n` is the number of units that haven't been consumed yet.

NOTE: The main reason `n` is a type parameter instead of a field is performance.
Because `n` is not a field, `buf` is the only non-Prop field, so `Input` is erased during compilation.
-/
structure Input (σ τ : Type) [Buffer σ τ] (n : Nat) where
  buf : σ
  valid : n ≤ size τ buf

namespace Input

variable {σ τ : Type} [Buffer σ τ] {n m k : Nat}

abbrev nextTok (inp : Input σ τ n) : Option τ := Buffer.nextTok inp.buf n

theorem width_le
  {t : τ}
  (inp : Input σ τ n)
  (h : inp.nextTok = some t)
  : width σ t ≤ n :=
  Buffer.nextTok_le h

theorem sub_width_lt
  {t : τ}
  {inp : Input σ τ n}
  (h : inp.nextTok = some t)
  : n - width σ t < n :=
  Buffer.sub_width_lt h

@[simp] theorem nextTok_eq_none {inp : Input σ τ 0} : inp.nextTok = none :=
  Buffer.nextTok_zero _

@[inline] def dropTo (inp : Input σ τ n) (m : Nat) (h : m ≤ n := by omega) : Input σ τ m where
  buf := inp.buf
  valid := h.trans inp.valid

@[simp] theorem dropTo_self (inp : Input σ τ n) (h : n ≤ n) : inp.dropTo n h = inp := rfl

@[simp] theorem dropTo_trans (inp : Input σ τ n) (h : m ≤ n) (h' : k ≤ m)
  : (inp.dropTo m h).dropTo k h' = inp.dropTo k (h'.trans h) := rfl

/-- Move past one token. -/
abbrev advance (inp : Input σ τ n) (t : τ) : Input σ τ (n - width σ t) :=
  inp.dropTo (n - width σ t)

/-- Skip forward while `f` holds, returning the number of units left unconsumed. -/
@[specialize] def skipWhile (f : τ → Bool) {n : Nat} (inp : Input σ τ n) : {m : Nat // m ≤ n} :=
  match h : inp.nextTok with
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

variable {f : τ → Bool} {t : τ} {inp : Input σ τ n}

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
  (h : inp.nextTok = none := by assumption)
  : (skipWhile f inp).val = n := by
  rw [skipWhile]; split <;> simp_all

end

/-- The scanners make progress exactly when the next token is accepted. -/
theorem skipWhile_lt_iff {f : τ → Bool} {inp : Input σ τ n}
  : (skipWhile f inp).val < n ↔ ∃ t, inp.nextTok = some t ∧ f t := by
  fun_cases skipWhile f inp <;> simp_all; omega

def ofArray {τ : Type} (a : Array τ) : Input (Array τ) τ a.size where
  buf := a
  valid := by simp

def ofByteArray (b : ByteArray) : Input ByteArray UInt8 b.size where
  buf := b
  valid := by simp

section Bytes

variable {n : Nat}

@[inline] def pos {τ : Type} [Buffer ByteArray τ] (inp : Input ByteArray τ n) : Nat :=
  inp.buf.size - n

theorem pos_lt (inp : Input ByteArray Char (n + 1)) : inp.pos < inp.buf.size := by
  have := inp.valid; simp only [pos, size_byteArray] at *; omega

@[inline] def head (inp : Input ByteArray Char (n + 1)) : UInt8 :=
  have := inp.pos_lt
  inp.buf[inp.pos]

def ofString (s : String) : Input ByteArray Char s.toUTF8.size where
  buf := s.toUTF8
  valid := by simp

/-- Collect characters while `f` holds, returning them as a `String`. -/
@[specialize] def takeWhile (f : Char → Bool) {n : Nat} (inp : Input ByteArray Char n) : String :=
  go inp ""
where
  @[specialize] go {m : Nat} (inp : Input ByteArray Char m) (acc : String) : String :=
    match h : inp.nextTok with
    | some c =>
      if f c then
        have : c.utf8Size ≤ m := by simpa using inp.width_le h
        have := Char.utf8Size_pos c
        go (inp.advance c) (acc.push c)
      else acc
    | none => acc
  termination_by m

variable {f : Char → Bool} {c : Char} {inp : Input ByteArray Char n} {acc : String}

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
  (h : inp.nextTok = none := by assumption)
  : takeWhile.go f inp acc = acc := by
  rw [takeWhile.go]; split <;> simp_all

theorem takeWhile_reject
  (h : inp.nextTok = some c := by assumption)
  (hf : ¬ f c := by assumption)
  : takeWhile f inp = "" := by rw [takeWhile, takeWhile_go_reject]

theorem takeWhile_eof
  (h : inp.nextTok = none)
  : takeWhile f inp = "" := by rw [takeWhile, takeWhile_go_eof]

private theorem utf8ByteSize_takeWhile_go
  (f : Char → Bool)
  (inp : Input ByteArray Char n)
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
  (inp : Input ByteArray Char n)
  : (takeWhile f inp).utf8ByteSize + (skipWhile f inp).val = n := by
  simp [takeWhile, utf8ByteSize_takeWhile_go]

theorem val_skipWhile
  (f : Char → Bool)
  (inp : Input ByteArray Char n)
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

theorem utf8ByteSize_takeWhile_pos_iff (f : Char → Bool) (inp : Input ByteArray Char n)
  : 0 < (takeWhile f inp).utf8ByteSize ↔ ∃ c, inp.nextTok = some c ∧ f c := by
  rw [← skipWhile_lt_iff]
  have := utf8ByteSize_takeWhile f inp
  omega

end Bytes

end Input
