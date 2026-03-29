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

private def keyword (s : String) : Parser Error .conditional PUnit :=
  lexeme (string s)

private def jnull : Parser Error .conditional Json :=
  (fun _ => .null) <$>ᵍ keyword "null"

private def jbool : Parser Error .conditional Json :=
  (fun _ => Json.bool true) <$>ᵍ keyword "true"
  <|> (fun _ => Json.bool false) <$>ᵍ keyword "false"

private def jnum : Parser Error .conditional Json :=
  .num <$>ᵍ lexeme nat

private def stringLit : Parser Error .conditional String := gdo
  dquote
  let cs ← many (satisfy (· != '\"'))
  dquote
  return String.ofList cs
  grade_by by simp

private def jstring : Parser Error .conditional Json :=
  .str <$>ᵍ lexeme stringLit

def json : Parser Error .conditional Json :=
  fix (fun json_rec =>
    let jarray : Parser Error .conditional Json := gdo
      let items ← brackets (sepBy (lexeme comma) json_rec)
      return .arr items
      grade_by by simp
    let jpair : Parser Error .conditional (String × Json) := gdo
      let k ← lexeme stringLit
      lexeme (char ':')
      let v ← json_rec
      return (k, v)
      grade_by by simp
    let jobject : Parser Error .conditional Json := gdo
      let kvs ← braces (sepBy (lexeme comma) jpair)
      return .obj kvs
      grade_by by simp
    oneOf [jnull, jbool, jnum, jstring, jarray, jobject])

end Json
