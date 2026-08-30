import PrimParser.Utf8

open Parser Parser.Utf8

/-! A [RFC 8259](https://www.rfc-editor.org/rfc/rfc8259) JSON parser. -/

namespace Parser.Json

/-- Can only be constructed by the `number` parser. -/
structure Number where
  private mk ::
  raw : String
  deriving Repr, BEq

inductive Value where
  | null
  | bool (value : Bool)
  | number (value : Number)
  | string (value : String)
  | array (values : List Value)
  | object (members : List (String × Value))
  deriving Repr, BEq

@[inline] private def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

@[inline] private def whitespace : Utf8Parser Error flexible PUnit :=
  skipWhile isWhitespace

@[inline] private def lexeme {α : Type} {ge gc : Necessity}
    (p : Utf8Parser Error ⟨ge, gc⟩ α) :
    Utf8Parser Error ⟨ge, gc ⊔ possibly⟩ α := gdo
  let result ← p
  whitespace
  return result
  grade_by by simp

@[inline] private def symbol (c : Char) : Utf8Parser Error conditional PUnit :=
  lexeme (char c)

@[inline] private def keyword (word : String) (h : word ≠ "" := by decide) :
    Utf8Parser Error conditional PUnit :=
  lexeme (Utf8.string word h)

@[inline] private def asciiDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

@[inline] private def nonzeroDigit (c : Char) : Bool :=
  '1' ≤ c && c ≤ '9'

private def nonzeroInteger : Utf8Parser Error conditional String := gdo
  let first ← satisfy nonzeroDigit
  let rest ← takeWhile asciiDigit
  return first.toString ++ rest
  grade_by by simp

@[inline] private def integerPart : Utf8Parser Error conditional String :=
  ("0" <$ᵍ char '0') <|> nonzeroInteger

private def fractionPart : Utf8Parser Error conditional String := gdo
  char '.'
  let digits ← takeWhile1 asciiDigit
  return "." ++ digits

private def exponentPart : Utf8Parser Error conditional String := gdo
  let marker ← satisfy (fun c => c == 'e' || c == 'E')
  let sign ← optional (satisfy (fun c => c == '+' || c == '-'))
  let digits ← takeWhile1 asciiDigit
  let signText := (sign.map Char.toString).getD ""
  return marker.toString ++ signText ++ digits

def number : Utf8Parser Error conditional Number := gdo
  let sign ← optional ("-" <$ᵍ char '-')
  let integer ← integerPart
  let fraction ← optional fractionPart
  let exponent ← optional exponentPart
  return Number.mk (sign.getD "" ++ integer ++ fraction.getD "" ++ exponent.getD "")
  grade_by by simp

@[inline] private def isUnescaped (c : Char) : Bool :=
  c.val ≥ 0x20 && c != '\"' && c != '\\'

private def simpleEscape : Utf8Parser Error conditional String :=
  Char.toString <$>ᵍ token fun
    | '\"' => some '\"'
    | '\\' => some '\\'
    | '/' => some '/'
    | 'b' => some (Char.ofNat 8)
    | 'f' => some (Char.ofNat 12)
    | 'n' => some '\n'
    | 'r' => some '\r'
    | 't' => some '\t'
    | _ => none

private def hexQuad : Utf8Parser Error conditional Nat := gdo
  let a ← ASCII.hexDigit
  let b ← ASCII.hexDigit
  let c ← ASCII.hexDigit
  let d ← ASCII.hexDigit
  return a.val * 0x1000 + b.val * 0x100 + c.val * 0x10 + d.val

private def decodedCodeUnit (first : Nat) : Utf8Parser Error fallible String :=
  if first ≥ 0xD800 && first ≤ 0xDBFF then
    weaken <| gdo
      char '\\'
      char 'u'
      let second ← hexQuad
      if second ≥ 0xDC00 && second ≤ 0xDFFF then
        let scalar := 0x10000 + (first - 0xD800) * 0x400 + (second - 0xDC00)
        ok (ge := possibly) (gc := possibly) (Char.ofNat scalar).toString
      else
        throw (ge := possibly) (gc := possibly) Error.fail
  else if first ≥ 0xDC00 && first ≤ 0xDFFF then
    throw (ge := possibly) (gc := possibly) Error.fail
  else
    ok (ge := possibly) (gc := possibly) (Char.ofNat first).toString

private def unicodeEscape : Utf8Parser Error conditional String := gdo
  char 'u'
  let first ← hexQuad
  decodedCodeUnit first
  grade_by by simp

private def escapedChar : Utf8Parser Error conditional String := gdo
  char '\\'
  simpleEscape <|> unicodeEscape

private def stringBodyGo {n : Nat} (t : Input ByteArray n) (acc : String) :
    Outcome Error n always String :=
  let chunk := t.takeWhile isUnescaped
  let m := n - chunk.utf8ByteSize
  have hm : m ≤ n := Nat.sub_le n chunk.utf8ByteSize
  let rest := t.dropTo m hm
  match h : rest.nextTok (τ := Char) with
  | none => failure { error := Error.eof, restSize := m }
  | some c =>
    if c == '\"' then
      success {
        result := acc ++ chunk
        restSize := m - c.utf8Size
        witness := by
          have hc := rest.width_le h
          simp only [Reader.width_byteArray] at hc
          have hp := Char.utf8Size_pos c
          omega }
    else if c == '\\' then
      match he : escapedChar.run rest with
      | .failure e => failure (e.trans hm)
      | .success e =>
        have he_lt : e.restSize < n := by
          have := e.witness
          omega
        match stringBodyGo (rest.dropTo e.restSize e.le) (acc ++ chunk ++ e.result) with
        | .failure f => failure (f.trans (Nat.le_trans e.le hm))
        | .success r => success {
          result := r.result
          restSize := r.restSize
          witness := by
            have hr := r.witness
            omega }
    else
      failure {
        error := Error.fail
        restSize := m - c.utf8Size
        witness := by omega }
termination_by n

private def stringBody : Utf8Parser Error conditional String where
  run t := stringBodyGo t ""

def string : Utf8Parser Error conditional String := gdo
  char '\"'
  stringBody

@[inline] private def nullValue : Utf8Parser Error conditional Value :=
  Value.null <$ᵍ keyword "null"

@[inline] private def trueValue : Utf8Parser Error conditional Value :=
  Value.bool true <$ᵍ keyword "true"

@[inline] private def falseValue : Utf8Parser Error conditional Value :=
  Value.bool false <$ᵍ keyword "false"

@[inline] private def numberValue : Utf8Parser Error conditional Value :=
  Value.number <$>ᵍ lexeme number

@[inline] private def stringValue : Utf8Parser Error conditional Value :=
  Value.string <$>ᵍ lexeme string

def value : Utf8Parser Error conditional Value :=
  fix fun value =>
    let arrayValue : Utf8Parser Error conditional Value := gdo
      symbol '['
      let values ← sepBy (symbol ',') value
      symbol ']'
      return .array values
    let member : Utf8Parser Error conditional (String × Value) := gdo
      let name ← lexeme string
      symbol ':'
      let memberValue ← value
      return (name, memberValue)
    let objectValue : Utf8Parser Error conditional Value := gdo
      symbol '{'
      let members ← sepBy (symbol ',') member
      symbol '}'
      return .object members
    oneOf (nullValue ::₁
      [trueValue, falseValue, numberValue, stringValue, arrayValue, objectValue])

/-- Parse a JSON document. -/
def json : Utf8Parser Error conditional Value := gdo
  whitespace
  let result ← value
  eof
  return result
  grade_by by simp

end Parser.Json
