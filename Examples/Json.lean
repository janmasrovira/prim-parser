-- Simplified JSON parser:
-- - Numbers: natural numbers only (no negatives, decimals, or exponents)
-- - Strings: no escape sequences (\n, \\, \uXXXX, etc.)
import PrimParser

open Parser Parser.Char

inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Nat)
  | str (s : String)
  | arr (xs : List Json)
  | obj (kvs : List (String × Json))
  deriving Repr, BEq

namespace Json

private def keyword (s : String) (h : s ≠ "" := by decide) : Utf8Parser Error conditional PUnit :=
  lexeme (string s h)

private def jnull : Utf8Parser Error conditional Json :=
  .null <$ᵍ keyword "null"

private def jbool : Utf8Parser Error conditional Json :=
  Json.bool true <$ᵍ keyword "true"
  <|> Json.bool false <$ᵍ keyword "false"

private def jnum : Utf8Parser Error conditional Json :=
  .num <$>ᵍ lexeme nat

private def stringLit : Utf8Parser Error conditional String := gdo
  dquote
  let cs ← many (satisfy (· != '\"'))
  dquote
  return String.ofList cs

private def jstring : Utf8Parser Error conditional Json :=
  .str <$>ᵍ lexeme stringLit

def json : Utf8Parser Error conditional Json :=
  fix (fun json_rec =>
    let jarray : Utf8Parser Error conditional Json := gdo
      let items ← brackets (sepBy (lexeme comma) json_rec)
      return .arr items
    let jpair : Utf8Parser Error conditional (String × Json) := gdo
      let k ← lexeme stringLit
      lexeme (char ':')
      let v ← json_rec
      return (k, v)
    let jobject : Utf8Parser Error conditional Json := gdo
      let kvs ← braces (sepBy (lexeme comma) jpair)
      return .obj kvs
    oneOf (jnull ::₁ [jbool, jnum, jstring, jarray, jobject]))

end Json
