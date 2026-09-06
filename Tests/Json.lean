import PrimParser.Json

open Parser Parser.Utf8 Parser.Json

#guard json.runOption "null" == some .null
#guard json.runOption " true\r\n" == some (.bool true)

#guard match json.runOption "-12.34e+56" with
  | some (.number n) => n.raw == "-12.34e+56"
  | _ => false

#guard json.runOption "\"hello, 世界\"" == some (.string "hello, 世界")
#guard json.runOption "\"\\\"\\\\\\/\\b\\f\\n\\r\\t\"" ==
  some (.string ("\"\\/" ++ String.ofList
    [Char.ofNat 8, Char.ofNat 12, '\n', '\r', '\t']))
#guard json.runOption "\"\\u0000\"" ==
  some (.string (String.singleton (Char.ofNat 0)))
#guard json.runOption "\"\\u20ac\"" == some (.string "€")
#guard json.runOption "\"\\uD834\\uDD1E\"" == some (.string "𝄞")

#guard match json.runOption "[null,true,-2.5,\"x\"]" with
  | some (.array [.null, .bool true, .number n, .string "x"]) => n.raw == "-2.5"
  | _ => false

#guard match json.runOption "{\"a\":1,\"a\":2}" with
  | some (.object [("a", .number a), ("a", .number b)]) =>
    a.raw == "1" && b.raw == "2"
  | _ => false

#guard json.runOption "{\"nested\":{\"ok\":true}}" ==
  some (.object [("nested", .object [("ok", .bool true)])])
#guard json.runOption "{\"\\u0061\":null}" == some (.object [("a", .null)])

#guard json.runOption "nul" == none
#guard json.runOption "" == none
#guard json.runOption "é" == none
#guard json.runOption "[]" == some (.array [])
#guard json.runOption "{}" == some (.object [])
