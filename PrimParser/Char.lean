import PrimParser.Basic

/-!
# Character parsers
-/

namespace Parser

variable
  {α β γ ε ε' : Type}
  {n m : Nat}
  {g g' : Grade}
  {ge ge' : Necessity} -- used for `errors`
  {gc gc' : Necessity} -- used for `consumes`

/-- Run a parser on a `String`. -/
def runParser (p : Parser ε g α) (s : String) : Except ε α :=
  p.runOn (Text.ofString s)

theorem runParser_sound (p : Parser ε g α) (s : String)
  : Except.Sound g.errors (p.runParser s) :=
  p.runOn_sound _

/-- Run a parser on a `String`, discarding the error and returning the value as an `Option`. -/
def runOption (p : Parser ε ⟨ge, gc⟩ α) (s : String) : Option α :=
  (p.runParser s).toOption

/-- Consume a single byte. -/
def anyByte : Parser Error conditional UInt8 where
  run {n} t := match n, t with
    | 0, _ => failure { error := Error.eof, restSize := 0 }
    | m + 1, t => success { result := t.head, restSize := m }

/-- Match a specific character. -/
def char (c : Char) : Parser Error conditional PUnit :=
  skipSatisfy (· == c)

/-- Match an exact non-empty string -/
def string (str : String) (h : str ≠ "" := by decide) : Parser Error conditional PUnit :=
  let rec go (c : Char) : List Char → Parser Error conditional PUnit
    | [] => skipSatisfy (· == c)
    | c' :: cs => gdo
      skipSatisfy (· == c)
      go c' cs
  match s : str.toList with
  | [] => by simp_all
  | c :: cs => go c cs

/-- Consume characters while `f` holds, returning the collected string. -/
def takeWhile (f : Char → Bool) : Parser Error flexible String :=
  String.ofList <$>ᵍ many (satisfy f)

@[specialize] private def takeWhileImpl (f : Char → Bool) : Parser Error flexible String where
  run {n} t :=
    let s := t.takeWhile f
    success { result := s
              restSize := n - s.utf8ByteSize }

/-- Consume one or more characters while `f` holds. -/
def takeWhile1 (f : Char → Bool) : Parser Error conditional String :=
  (String.ofList ∘ NonEmptyList.toList) <$>ᵍ many1 (satisfy f)

@[specialize] private def takeWhile1Impl (f : Char → Bool) : Parser Error conditional String where
  run {n} t := match n, t with
    | 0, _ =>
      failure { error := Error.eof
                restSize := 0 }
    | n + 1, t =>
      let s := t.takeWhile f
      if _h : 0 < s.utf8ByteSize then
        success { result := s
                  restSize := n + 1 - s.utf8ByteSize }
      else
        match hd : t.nextChar with
        | some c =>
          failure { error := Error.fail
                    restSize := n + 1 - c.utf8Size }
        | none =>
          failure { error := Error.eof
                    restSize := n + 1 }

/-- Skip characters while `f` holds. -/
def skipWhile (f : Char → Bool) : Parser Error flexible PUnit :=
  () <$ᵍ takeWhile f

@[specialize] private def skipWhileImpl (f : Char → Bool) : Parser Error flexible PUnit where
  run t :=
    let r := t.skipWhile f
    success { result := ()
              restSize := r.val }

/-- Skip one or more characters while `f` holds. -/
def skipWhile1 (f : Char → Bool) : Parser Error conditional PUnit :=
  () <$ᵍ takeWhile1 f

@[specialize] private def skipWhile1Impl (f : Char → Bool) : Parser Error conditional PUnit where
  run {n} t := match n, t with
    | 0, _ =>
      failure { error := Error.eof
                restSize := 0 }
    | n + 1, t =>
      let r := t.skipWhile f
      if _h : r.val < n + 1 then
        success { result := ()
                  restSize := r.val }
      else
        match hd : t.nextChar with
        | some c =>
          failure { error := Error.fail
                    restSize := n + 1 - c.utf8Size }
        | none =>
          failure { error := Error.eof
                    restSize := n + 1 }

theorem many_go_satisfy_restSize
  (f : Char → Bool)
  (t : Text n)
  : (many.go (satisfy f) t).restSize = (Text.skipWhile f t).val := by
  fun_induction Text.skipWhile f t <;> rw [many.go]
  case case1 => rw [satisfy_run_accept]; assumption
  case case2 => simp_all [satisfy_run_reject]
  case case3 => simp_all [satisfy_run_eof]

/-- The only step that is specific to the `String` accumulator. -/
private theorem ofList_eq_foldl (l : List Char) : String.ofList l = l.foldl String.push "" := by
  suffices h : ∀ acc, l.foldl String.push acc = acc ++ String.ofList l by
    simp only [h, String.empty_append]
  intro acc
  induction l generalizing acc with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, ih, String.push_eq_append, String.ofList_cons,
               String.append_assoc]

private theorem takeWhile_go_eq (f : Char → Bool) (t : Text n) (acc : String)
  : Text.takeWhile.go f t acc = (many.go (satisfy f) t).result.foldl String.push acc := by
  fun_induction Text.takeWhile.go f t acc <;> rw [many.go]
  case case1 => rw [satisfy_run_accept]; simp_all
  case case2 => simp_all [satisfy_run_reject]
  case case3 => simp_all [satisfy_run_eof]

theorem many_go_satisfy_result (f : Char → Bool) (t : Text n)
  : String.ofList (many.go (satisfy f) t).result = Text.takeWhile f t := by
  rw [ofList_eq_foldl, Text.takeWhile, takeWhile_go_eq]

@[csimp] private theorem takeWhile_eq_impl : @takeWhile = @takeWhileImpl := by
  funext f
  simp only [takeWhile, takeWhileImpl, many, GradedFunctor.gmap, Functor.map,
             many_go_satisfy_result, many_go_satisfy_restSize, Text.val_skipWhile]

@[csimp] private theorem skipWhile_eq_impl : @skipWhile = @skipWhileImpl := by
  funext f
  simp only [skipWhile, takeWhile, skipWhileImpl, many, GradedFunctor.gmap, Functor.map,
             many_go_satisfy_restSize]
  rfl

private theorem many1_satisfy_eq (f : Char → Bool)
  : many1 (satisfy f)
    = (satisfy f >>=ᵍ fun c => many (satisfy f) >>=ᵍ fun cs => gpure (c ::₁ cs)) := rfl

section

variable {f : Char → Bool} {c : Char} {t : Text n}

theorem takeWhile1_run_accept
  (h : t.nextChar = some c := by assumption)
  (hf : f c := by assumption)
  : (takeWhile1 f).run t
    = success { result := Text.takeWhile f t
                restSize := (Text.skipWhile f t).val
                witness := Text.skipWhile_lt_iff.mpr ⟨c, h, hf⟩ } := by
  have := t.utf8Size_le h
  have := Char.utf8Size_pos c
  have hres : (many.go (satisfy f) t).result
       = c :: (many.go (satisfy f) (t.advance c)).result := by
    rw [many.go, satisfy_run_accept]
  have hrest : (many.go (satisfy f) t).restSize
      = (many.go (satisfy f) (t.advance c)).restSize := by
    rw [many.go, satisfy_run_accept]
  simp only [takeWhile1, GradedFunctor.gmap, many1_satisfy_eq, gbind_run]
  rw [Outcome.handle_success satisfy_run_accept]
  simp only [Success.bindParser, many, gbind_run, GradedApplicative.gpure, Outcome.handle,
             Success.seq, Functor.map, Function.comp_apply, NonEmptyList.mk, NonEmptyList.toList,
             ← hres, ← hrest, many_go_satisfy_result, many_go_satisfy_restSize]

/-- `takeWhile1` fails exactly as the leading `satisfy` does. -/
theorem takeWhile1_run_failure {fl : Failure n Error}
  (hs : (satisfy f).run t = failure fl)
  : (takeWhile1 f).run t = failure fl := by
  simp only [takeWhile1, GradedFunctor.gmap, many1_satisfy_eq, gbind_run]
  rw [Outcome.handle_failure hs]
  rfl

end

@[csimp] private theorem takeWhile1_eq_impl : @takeWhile1 = @takeWhile1Impl := by
  ext f n t
  simp only [takeWhile1Impl, Text.utf8ByteSize_takeWhile_pos_iff]
  repeat1' split
  next => exact takeWhile1_run_failure satisfy_run_eof
  next haccepts =>
    obtain ⟨c, hd, hf⟩ := haccepts
    simp only [takeWhile1_run_accept hd hf, Text.val_skipWhile]
  next hrejects c hd =>
    have : ¬ f c := fun hf => hrejects ⟨c, hd, hf⟩
    exact takeWhile1_run_failure satisfy_run_reject
  next => exact takeWhile1_run_failure satisfy_run_eof

section

variable {f : Char → Bool} {c : Char} {t : Text n}

theorem skipWhile1_run_accept
  (h : t.nextChar = some c)
  (hf : f c)
  : (skipWhile1 f).run t
    = success { result := ()
                restSize := (Text.skipWhile f t).val
                witness := Text.skipWhile_lt_iff.mpr ⟨c, h, hf⟩ } := by
  simp only [skipWhile1, gconst, GradedFunctor.gmap, Functor.map, takeWhile1_run_accept h hf]

/-- `skipWhile1` fails exactly as `takeWhile1` does. -/
theorem skipWhile1_run_failure {fl : Failure n Error}
  (hs : (satisfy f).run t = failure fl)
  : (skipWhile1 f).run t = failure fl := by
  simp only [skipWhile1, gconst, GradedFunctor.gmap, Functor.map, takeWhile1_run_failure hs]

end

@[csimp] private theorem skipWhile1_eq_impl : @skipWhile1 = @skipWhile1Impl := by
  ext f n t
  simp only [skipWhile1Impl, Text.skipWhile_lt_iff]
  repeat1' split
  next => exact skipWhile1_run_failure satisfy_run_eof
  next haccepts =>
    obtain ⟨c, hd, hf⟩ := haccepts
    exact skipWhile1_run_accept hd hf
  next hrejects c hd =>
    have : ¬ f c := fun hf => hrejects ⟨c, hd, hf⟩
    exact skipWhile1_run_failure satisfy_run_reject
  next => exact skipWhile1_run_failure satisfy_run_eof

/-- Skip zero or more whitespace characters. -/
def whitespace : Parser Error flexible PUnit :=
  skipWhile Char.isWhitespace

/-- Skip one or more whitespace characters. -/
def whitespace1 : Parser Error conditional PUnit :=
  skipWhile1 Char.isWhitespace

/-- Run `p` then skip trailing whitespace. -/
def lexeme (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge, gc ⊔ possibly⟩ α := gdo
  let r ← p
  whitespace
  return r
  grade_by by simp

def lparen   := char '('
def rparen   := char ')'
def lbracket := char '['
def rbracket := char ']'
def lbrace   := char '{'
def rbrace   := char '}'
def dquote   := char '\"'
def comma    := char ','

/-- Parse `p` surrounded by the delimiters `l` and `r`. Delimiters consume whitespace after them. -/
def bracket (l r : Parser Error conditional PUnit) (p : Parser Error ⟨ge, gc⟩ α)
  : Parser Error ⟨ge ⊔ possibly, always⟩ α := rawBracket (lexeme l) (lexeme r) p

/-- Parse `p` surrounded by parentheses. -/
def parens (p : Parser Error ⟨ge, gc⟩ α)
  : Parser Error ⟨ge ⊔ possibly, always⟩ α := bracket lparen rparen p

/-- Parse `p` surrounded by square brackets. -/
def brackets (p : Parser Error ⟨ge, gc⟩ α)
  : Parser Error ⟨ge ⊔ possibly, always⟩ α := bracket lbracket rbracket p

/-- Parse `p` surrounded by curly braces. -/
def braces (p : Parser Error ⟨ge, gc⟩ α)
  : Parser Error ⟨ge ⊔ possibly, always⟩ α := bracket lbrace rbrace p

/-- Parse a single decimal digit, returning its numeric value. -/
def digit : Parser Error conditional Nat :=
  token fun c => if c.isDigit then some (c.toNat - '0'.toNat) else none

/-- Parse a natural number (one or more digits). -/
def nat : Parser Error conditional Nat := gdo
  let d ← digit
  let ds ← many digit
  return ds.foldl (fun acc d => acc * 10 + d) d

/-- Parse an integer (optional leading `-` followed by digits). -/
def int : Parser Error conditional Int := gdo
  let neg ← optional (char '-')
  let n ← nat
  return if neg.isSome then -n else n

def space : Parser Error conditional PUnit := skipSatisfy (· == ' ')

def tab : Parser Error conditional PUnit := skipSatisfy (· == '\t')

namespace ASCII

def lf : Parser Error conditional PUnit := skipSatisfy (· == '\n')

def cr : Parser Error conditional PUnit := skipSatisfy (· == '\r')

/-- Match an ASCII uppercase letter. -/
def uppercase : Parser Error conditional Char := satisfy Char.isUpper

/-- Match an ASCII lowercase letter. -/
def lowercase : Parser Error conditional Char := satisfy Char.isLower

/-- Match an ASCII letter. -/
def alpha : Parser Error conditional Char := satisfy Char.isAlpha

/-- Match an ASCII letter or digit. -/
def alphanum : Parser Error conditional Char := satisfy Char.isAlphanum

/-- Match an ASCII control character. -/
def control : Parser Error conditional Char :=
  satisfy fun c => c.val < 0x20 || c.val == 0x7F

/-- Match a binary digit. -/
def binDigit : Parser Error conditional Bool :=
  token fun
    | '0' => some false
    | '1' => some true
    | _   => none

/-- Match an octal digit, returning its numeric value. -/
def octDigit : Parser Error conditional (Fin 8) :=
  token fun
    | '0' => some 0
    | '1' => some 1
    | '2' => some 2
    | '3' => some 3
    | '4' => some 4
    | '5' => some 5
    | '6' => some 6
    | '7' => some 7
    | _ => none

/-- Match a hexadecimal digit, returning its numeric value. -/
def hexDigit : Parser Error conditional (Fin 16) :=
  token fun
    | '0' => some 0
    | '1' => some 1
    | '2' => some 2
    | '3' => some 3
    | '4' => some 4
    | '5' => some 5
    | '6' => some 6
    | '7' => some 7
    | '8' => some 8
    | '9' => some 9
    | 'a' | 'A' => some 10
    | 'b' | 'B' => some 11
    | 'c' | 'C' => some 12
    | 'd' | 'D' => some 13
    | 'e' | 'E' => some 14
    | 'f' | 'F' => some 15
    | _ => none

end ASCII

/-- Match a line terminator: LF or CRLF. -/
def eol : Parser Error conditional PUnit := gdo
  skipOptional ASCII.cr
  ASCII.lf

end Parser
