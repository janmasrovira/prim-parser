import PrimParser.Json

open Parser Parser.Json

private structure Counts where
  requiredPassed : Nat := 0
  requiredFailed : Nat := 0
  implementationAccepted : Nat := 0
  implementationRejected : Nat := 0

private def accepts (input : ByteArray) : Bool :=
  match json.runOn (Input.ofByteArray input) with
  | .ok _ => true
  | .error _ => false

private def fixtureKind (name : String) : Option (Bool × Bool) :=
  if name.startsWith "y_" then some (true, true)
  else if name.startsWith "n_" then some (true, false)
  else if name.startsWith "i_" then some (false, false)
  else none

private def runSuite (directory : System.FilePath) : IO Counts := do
  let entries ← System.FilePath.readDir directory
  let entries := entries.qsort (fun a b => a.fileName < b.fileName)
  let mut counts := {}
  for entry in entries do
    let name := entry.fileName
    if name.endsWith ".json" then
      match fixtureKind name with
      | none => pure ()
      | some (isRequired, expected) =>
        let input ← IO.FS.readBinFile entry.path
        let actual := accepts input
        if isRequired then
          if actual == expected then
            counts := { counts with requiredPassed := counts.requiredPassed + 1 }
          else
            counts := { counts with requiredFailed := counts.requiredFailed + 1 }
            IO.eprintln s!"FAIL {name}: expected {if expected then "accept" else "reject"}"
        else if actual then
          counts := { counts with implementationAccepted := counts.implementationAccepted + 1 }
        else
          counts := { counts with implementationRejected := counts.implementationRejected + 1 }
  return counts

def main (args : List String) : IO UInt32 := do
  let directory := System.FilePath.mk <| args.head?.getD "JSONTestSuite/test_parsing"
  if !(← directory.isDir) then
    IO.eprintln s!"JSONTestSuite fixture directory not found: {directory}"
    IO.eprintln "Pass the path to JSONTestSuite/test_parsing as the first argument."
    return 2
  let counts ← runSuite directory
  IO.println s!"required: {counts.requiredPassed} passed, {counts.requiredFailed} failed"
  IO.println s!"implementation-defined: {counts.implementationAccepted} accepted, \
    {counts.implementationRejected} rejected"
  return if counts.requiredFailed == 0 then 0 else 1
