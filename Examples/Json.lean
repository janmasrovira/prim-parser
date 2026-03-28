-- Simplified JSON parser:
-- - Numbers: natural numbers only (no negatives, decimals, or exponents)
-- - Strings: no escape sequences (\n, \\, \uXXXX, etc.)
import PrimParser

open Parser

inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Nat)
  | str (s : String)
  | arr (xs : List Json)
  | obj (kvs : List (String × Json))
  deriving Repr, BEq

namespace Json

private def lchar (c : Char) : Parser Error .conditional PUnit :=
  lexeme (char c)

private def keyword (s : String) : Parser Error .conditional PUnit :=
  lexeme (string s)

private def jnull : Parser Error .conditional Json :=
  (fun _ => .null) <$>ᵍ keyword "null"

private def jbool : Parser Error .conditional Json :=
  choice
    ((fun _ => .bool true) <$>ᵍ keyword "true")
    ((fun _ => .bool false) <$>ᵍ keyword "false")

private def jnum : Parser Error .conditional Json :=
  .num <$>ᵍ lexeme nat

private def dquotes := char '\"'

private def stringLit : Parser Error .conditional String := gdo
  dquotes
  let cs ← many (satisfy (· != '\"'))
  dquotes
  return String.ofList cs
  grade_by by simp

private def jstring : Parser Error .conditional Json :=
  .str <$>ᵍ lexeme stringLit

def json : Parser Error .conditional Json :=
  fix (fun json_rec =>
    let jarray : Parser Error .conditional Json := gdo
      lchar '['
      let items ← sepBy json_rec (lchar ',')
      lchar ']'
      return .arr items
      grade_by by simp
    let jpair : Parser Error .conditional (String × Json) := gdo
      let k ← lexeme stringLit
      lchar ':'
      let v ← json_rec
      return (k, v)
      grade_by by simp
    let jobject : Parser Error .conditional Json := gdo
      lchar '{'
      let kvs ← sepBy jpair (lchar ',')
      lchar '}'
      return .obj kvs
      grade_by by simp
    oneOf [jnull, jbool, jnum, jstring, jarray, jobject])

end Json
