/-
Benchmark harness (root of the `bench` executable, copied per ref by run.sh).
Uses only API stable across the refs being compared.

  bench <workload: json|arith|csv|bytes> <size> <iters>
  bench json-file <path> <iters>
-/
import Examples.Json
import Examples.Arith
import Examples.Csv
import PrimParser.Byte
import PrimParser.Json

open Parser Parser.Utf8 Parser.Byte

/-- Build a length-indexed `Input` from a `String`. -/
def toInput (s : String) : Input ByteArray s.toUTF8.size := Input.ofString s

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

def genBytes (n : Nat) : ByteArray :=
  ((List.range (21 * max 1 n)).map (fun i => UInt8.ofNat (i * 7 % 251))).toByteArray

def record : ByteParser Error conditional UInt64 := gdo
  let a ← uint8
  let b ← uint16be
  let c ← uint32le
  let d ← uint64be
  let e ← int16be
  let f ← int32le
  return a.toUInt64 + b.toUInt64 + c.toUInt64 + d + e.toUInt16.toUInt64 + f.toUInt32.toUInt64

/-- Run `body` `iters` times, summing the returned tallies (keeps the work live). -/
def loop (iters : Nat) (body : Unit → Nat) : Nat :=
  (List.range iters).foldl (fun acc _ => acc + body ()) 0

def benchJson (size iters : Nat) : Nat :=
  let t := toInput (genJson size)
  loop iters fun _ =>
    match Json.json.run t with
    | Parser.success r => match r.result with
      | .arr xs => xs.length
      | _ => 0
    | Parser.failure _ => 0

def benchJsonFile (input : ByteArray) (iters : Nat) : Nat :=
  let t := Input.ofByteArray input
  loop iters fun _ =>
    match Parser.Json.document.run t with
    | Parser.success r => match r.result with
      | .object members => members.length
      | .array values => values.length
      | _ => 1
    | Parser.failure _ => 0

def benchArith (size iters : Nat) : Nat :=
  let t := toInput (genArith size)
  loop iters fun _ =>
    match Expr.expr.run t with
    | Parser.success r => (Expr.eval r.result).toNat
    | Parser.failure _ => 0

def benchCsv (size iters : Nat) : Nat :=
  let t := toInput (genCsv size)
  loop iters fun _ =>
    match Csv.table.run t with
    | Parser.success r => r.result.fst
    | Parser.failure _ => 0

def benchBytes (size iters : Nat) : Nat :=
  let t := Input.ofByteArray (genBytes size)
  loop iters fun _ =>
    match (many record).run t with
    | Parser.success r => (r.result.foldl (· + ·) 0).toNat % 1000000
    | Parser.failure _ => 0

def main (args : List String) : IO Unit := do
  let workload := args[0]?.getD "json"
  if workload == "json-file" then
    let path := System.FilePath.mk <| args[1]?.getD "bench/data/citm_catalog.json"
    let iters := (args[2]?.bind String.toNat?).getD 100
    let input ← IO.FS.readBinFile path
    let tally := benchJsonFile input iters
    if tally == 0 then
      throw (IO.userError s!"failed to parse JSON fixture: {path}")
    IO.println s!"{workload} file={path} bytes={input.size} iters={iters} tally={tally}"
  else
    let size := (args[1]?.bind String.toNat?).getD 1000
    let iters := (args[2]?.bind String.toNat?).getD 100
    let tally ←
      match workload with
      | "json"  => pure (benchJson size iters)
      | "arith" => pure (benchArith size iters)
      | "csv"   => pure (benchCsv size iters)
      | "bytes" => pure (benchBytes size iters)
      | other   => throw (IO.userError s!"unknown workload: {other}")
    IO.println s!"{workload} size={size} iters={iters} tally={tally}"
