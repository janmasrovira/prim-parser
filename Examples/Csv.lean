-- Simple CSV parser:
-- - Unquoted fields: any characters except comma, double-quote, newline
-- - Quoted fields: enclosed in double-quotes, with "" as escaped quote
-- - Rows separated by newline (\n)
import PrimParser

open Parser

namespace Csv

private def comma := char ','
private def dquote := char '\"'
private def newline := char '\n'

private def escapedQuote : Parser Error .conditional Char := gdo
  dquote
  dquote
  return '\"'
  grade_by by simp

private def quotedField : Parser Error .conditional String := gdo
  dquote
  let cs ← many (choice escapedQuote (satisfy (· != '\"')))
  dquote
  return String.ofList cs
  grade_by by simp

private def unquotedField : Parser Error .flexible String :=
  takeWhile (fun c => c != ',' && c != '\"' && c != '\n')

private def field : Parser Error .flexible String :=
  choice quotedField unquotedField

def row : Parser Error .flexible (List String) :=
  sepBy comma field

def csv : Parser Error .flexible (List (List String)) :=
  sepBy newline row

end Csv
