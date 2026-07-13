/-
Benchmark harness (root of the `bench` executable, copied per ref by run.sh).
Uses only API stable across the refs being compared.

  bench <workload: json|arith|csv> <size> <iters>
-/
import Examples.Json
import Examples.Arith
import Examples.Csv

open Parser

/-- Build a length-indexed `Text` from a `String`. -/
def toText (s : String) : Text s.toList.length := ⟨s.toList, rfl⟩

/-- `[0, 1, 2, ..., n-1]` as JSON. -/
def genJson (n : Nat) : String :=
  "[" ++ String.intercalate ", " ((List.range n).map toString) ++ "]"

/-- `1+2+3+...+n` (falls back to `1` when `n = 0`). -/
def genArith (n : Nat) : String :=
  match n with
  | 0 => "1"
  | _ => String.intercalate "+" ((List.range n).map (fun i => toString (i + 1)))

/-- `n` CSV rows, each `col0,col1,col2`. -/
def genCsv (n : Nat) : String :=
  String.intercalate "\n" ((List.range (max 1 n)).map (fun i =>
    s!"a{i},b{i},c{i}"))

/-- Run `body` `iters` times, summing the returned tallies (keeps the work live). -/
def loop (iters : Nat) (body : Unit → Nat) : Nat :=
  (List.range iters).foldl (fun acc _ => acc + body ()) 0

def benchJson (size iters : Nat) : Nat :=
  let t := toText (genJson size)
  loop iters fun _ =>
    match Json.json.runResult? t with
    | some (.arr xs) => xs.length
    | _ => 0

def benchArith (size iters : Nat) : Nat :=
  let t := toText (genArith size)
  loop iters fun _ =>
    match Expr.expr.runResult? t with
    | some e => (Expr.eval e).toNat
    | none => 0

def benchCsv (size iters : Nat) : Nat :=
  let t := toText (genCsv size)
  loop iters fun _ =>
    match Csv.table.runResult? t with
    | some ⟨n, _⟩ => n
    | none => 0

def main (args : List String) : IO Unit := do
  let workload := args[0]?.getD "json"
  let size := (args[1]?.bind String.toNat?).getD 1000
  let iters := (args[2]?.bind String.toNat?).getD 100
  let tally ←
    match workload with
    | "json"  => pure (benchJson size iters)
    | "arith" => pure (benchArith size iters)
    | "csv"   => pure (benchCsv size iters)
    | other   => throw (IO.userError s!"unknown workload: {other}")
  IO.println s!"{workload} size={size} iters={iters} tally={tally}"
