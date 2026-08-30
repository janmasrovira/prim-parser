import PrimParser.Utf8

open Parser Parser.Utf8

/-! An RFC 8259 JSON parser, developed independently from the intentionally
simplified parser in `Examples.Json`. -/

namespace Parser.Json

/-- JSON numbers are retained exactly as written. This avoids silently losing
precision and lets applications choose their own numeric representation. -/
structure Number where
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

private def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def whitespace : Utf8Parser Error flexible PUnit :=
  skipWhile isWhitespace

private def lexeme {α : Type} {ge gc : Necessity}
    (p : Utf8Parser Error ⟨ge, gc⟩ α) :
    Utf8Parser Error ⟨ge, gc ⊔ possibly⟩ α := gdo
  let result ← p
  whitespace
  return result
  grade_by by simp

private def keyword (word : String) (h : word ≠ "" := by decide) :
    Utf8Parser Error conditional PUnit :=
  lexeme (Utf8.string word h)

private def asciiDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

private def nonzeroDigit (c : Char) : Bool :=
  '1' ≤ c && c ≤ '9'

private def nonzeroInteger : Utf8Parser Error conditional String := gdo
  let first ← satisfy nonzeroDigit
  let rest ← takeWhile asciiDigit
  return first.toString ++ rest
  grade_by by simp

private def integerPart : Utf8Parser Error conditional String :=
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

/-- Parse the complete grammar for an RFC 8259 number. -/
def number : Utf8Parser Error conditional Number := gdo
  let sign ← optional ("-" <$ᵍ char '-')
  let integer ← integerPart
  let fraction ← optional fractionPart
  let exponent ← optional exponentPart
  return ⟨sign.getD "" ++ integer ++ fraction.getD "" ++ exponent.getD ""⟩
  grade_by by simp

private def nullValue : Utf8Parser Error conditional Value :=
  Value.null <$ᵍ keyword "null"

private def trueValue : Utf8Parser Error conditional Value :=
  Value.bool true <$ᵍ keyword "true"

private def falseValue : Utf8Parser Error conditional Value :=
  Value.bool false <$ᵍ keyword "false"

private def numberValue : Utf8Parser Error conditional Value :=
  Value.number <$>ᵍ lexeme number

private def primitive : Utf8Parser Error conditional Value :=
  oneOf (nullValue ::₁ [trueValue, falseValue, numberValue])

/-- Parse exactly one complete JSON document. Strings, arrays, and objects are
added in subsequent implementation steps. -/
def document : Utf8Parser Error conditional Value := gdo
  whitespace
  let value ← primitive
  eof
  return value
  grade_by by simp

end Parser.Json
