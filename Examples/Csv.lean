-- Simple CSV parser:
-- - First row is column names (headers)
-- - Subsequent rows are data, each row must have the same number of fields
-- - Each value is either an integer (possibly negative) or a string
-- - Quoted fields: enclosed in double-quotes, with "" as escaped quote
-- - Rows separated by newline (\n)
import PrimParser

open Parser

namespace Csv

inductive Value where
  | int (n : Int)
  | str (s : String)
  deriving Repr, BEq

instance {α : Type} {n : Nat} [BEq α] : BEq (List.Vector α n) where
  beq a b := a.toList == b.toList

instance {α : Type} {n : Nat} [Repr α] : Repr (List.Vector α n) where
  reprPrec v p := reprPrec v.toList p

structure Table (n : Nat) where
  columns : List.Vector String n
  rows : List (List.Vector Value n)
  deriving Repr, BEq

instance : BEq ((n : Nat) × Table n) where
  beq a b := a.1 == b.1 && a.1 == b.1 &&
    a.2.columns.toList == b.2.columns.toList &&
    a.2.rows.map List.Vector.toList == b.2.rows.map List.Vector.toList

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

private def int : Parser Error .conditional Int := gdo
  let neg ← optional (char '-')
  let n ← nat
  return if neg.isSome then -↑n else ↑n
  grade_by by simp

private def value : Parser Error .flexible Value :=
  choice (.int <$>ᵍ int) (.str <$>ᵍ unquotedField)

private def quotedValue : Parser Error .conditional Value := gdo
  let s ← quotedField
  return .str s

private def cell : Parser Error .flexible Value :=
  choice quotedValue value

def row : Parser Error .flexible (List String) :=
  sepBy comma field

private def exactRow (n : Nat) : Parser Error .fallible (List.Vector Value n) :=
  sepByN comma cell n

def table : Parser Error .conditional ((n : Nat) × Table n) := gdo
  let headers ← row
  newline
  let n := headers.length
  let rows ← sepBy newline (exactRow n)
  let t : Table n := { columns := ⟨headers, rfl⟩, rows }
  return (⟨n, t⟩ : (n : Nat) × Table n)
  grade_by by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one]

end Csv
