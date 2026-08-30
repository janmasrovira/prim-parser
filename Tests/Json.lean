import PrimParser.Json

open Parser Parser.Utf8 Parser.Json

private def parsedNumber (raw : String) : Value :=
  match json.runOption raw with
  | some value => value
  | none => .null

-- Literals and exact document boundaries.
#guard json.runOption "null" == some .null
#guard json.runOption " true\r\n" == some (.bool true)
#guard json.runOption "false trailing" == none
#guard json.runOption "" == none

-- Complete RFC 8259 number grammar.
#guard (json.runOption "0").map (fun | .number n => some n.raw | _ => none) == some (some "0")
#guard (json.runOption "-0").map (fun | .number n => some n.raw | _ => none) == some (some "-0")
#guard (json.runOption "123").map (fun | .number n => some n.raw | _ => none) == some (some "123")
#guard (json.runOption "-12.34e+56").map (fun | .number n => some n.raw | _ => none) ==
  some (some "-12.34e+56")
#guard (json.runOption "1E-9").map (fun | .number n => some n.raw | _ => none) ==
  some (some "1E-9")

-- Invalid number forms represented by JSONTestSuite's `n_number_*` cases.
#guard json.runOption "01" == none
#guard json.runOption "-01" == none
#guard json.runOption "+1" == none
#guard json.runOption ".1" == none
#guard json.runOption "1." == none
#guard json.runOption "1e" == none
#guard json.runOption "1e+" == none
#guard json.runOption "--1" == none

-- RFC whitespace is deliberately narrower than Unicode whitespace.
#guard (json.runOption "\t\n\r 0 \r\n\t").map (fun | .number n => some n.raw | _ => none) ==
  some (some "0")
#guard json.runOption (String.singleton (Char.ofNat 11) ++ "0") == none

-- Strings and the eight short escapes.
#guard json.runOption "\"\"" == some (.string "")
#guard json.runOption "\"hello, 世界\"" == some (.string "hello, 世界")
#guard json.runOption "\"line separator\"" == some (.string "line separator")
#guard json.runOption "\"\\\"\\\\\\/\\b\\f\\n\\r\\t\"" ==
  some (.string ("\"\\/" ++ String.ofList
    [Char.ofNat 8, Char.ofNat 12, '\n', '\r', '\t']))
#guard json.runOption "\"\\u0000\"" ==
  some (.string (String.singleton (Char.ofNat 0)))
#guard json.runOption "\"\\u20ac\"" == some (.string "€")
#guard json.runOption "\"\\uD834\\uDD1E\"" == some (.string "𝄞")

-- Raw controls, malformed escapes, and unpaired UTF-16 surrogates are invalid.
#guard json.runOption ("\"a" ++ String.singleton (Char.ofNat 10) ++ "b\"") == none
#guard json.runOption "\"\\x\"" == none
#guard json.runOption "\"\\u12x4\"" == none
#guard json.runOption "\"\\uD834\"" == none
#guard json.runOption "\"\\uDD1E\"" == none
#guard json.runOption "\"\\uD834\\u0041\"" == none
#guard json.runOption "\"\\uDD1E\\uD834\"" == none
#guard json.runOption "\"\\uD834\\uD834\"" == none
#guard json.runOption "\"unterminated" == none

-- Arrays, including heterogeneous and recursive values.
#guard json.runOption "[]" == some (.array [])
#guard json.runOption "[null,true,-2.5,\"x\"]" == some (.array
  [.null, .bool true, parsedNumber "-2.5", .string "x"])
#guard json.runOption "[[],[{}]]" == some (.array
  [.array [], .array [.object []]])
#guard json.runOption "[ \n 1 ,\t 2 \r]" == some (.array
  [parsedNumber "1", parsedNumber "2"])

-- Objects preserve member order and duplicate names.
#guard json.runOption "{}" == some (.object [])
#guard json.runOption "{\"a\":1,\"b\":[false]}" == some (.object
  [("a", parsedNumber "1"), ("b", .array [.bool false])])
#guard json.runOption "{\"a\":1,\"a\":2}" == some (.object
  [("a", parsedNumber "1"), ("a", parsedNumber "2")])
#guard json.runOption " { \"nested\" : { \"ok\" : true } } " == some (.object
  [("nested", .object [("ok", .bool true)])])
#guard json.runOption "{\"\\u0061\":null}" == some (.object [("a", .null)])

-- Separators and delimiters are strict.
#guard json.runOption "[1,]" == none
#guard json.runOption "[,1]" == none
#guard json.runOption "[1,,2]" == none
#guard json.runOption "[1 2]" == none
#guard json.runOption "[" == none
#guard json.runOption "{\"a\":1,}" == none
#guard json.runOption "{,\"a\":1}" == none
#guard json.runOption "{\"a\" 1}" == none
#guard json.runOption "{\"a\":}" == none
#guard json.runOption "{1:true}" == none
#guard json.runOption "{" == none
#guard json.runOption "{\"a\":[1,2}" == none
