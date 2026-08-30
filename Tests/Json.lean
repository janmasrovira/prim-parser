import PrimParser.Json

open Parser Parser.Utf8 Parser.Json

-- Literals and exact document boundaries.
#guard document.runOption "null" == some .null
#guard document.runOption " true\r\n" == some (.bool true)
#guard document.runOption "false trailing" == none
#guard document.runOption "" == none

-- Complete RFC 8259 number grammar.
#guard document.runOption "0" == some (.number ⟨"0"⟩)
#guard document.runOption "-0" == some (.number ⟨"-0"⟩)
#guard document.runOption "123" == some (.number ⟨"123"⟩)
#guard document.runOption "-12.34e+56" == some (.number ⟨"-12.34e+56"⟩)
#guard document.runOption "1E-9" == some (.number ⟨"1E-9"⟩)

-- Invalid number forms represented by JSONTestSuite's `n_number_*` cases.
#guard document.runOption "01" == none
#guard document.runOption "-01" == none
#guard document.runOption "+1" == none
#guard document.runOption ".1" == none
#guard document.runOption "1." == none
#guard document.runOption "1e" == none
#guard document.runOption "1e+" == none
#guard document.runOption "--1" == none

-- RFC whitespace is deliberately narrower than Unicode whitespace.
#guard document.runOption "\t\n\r 0 \r\n\t" == some (.number ⟨"0"⟩)
#guard document.runOption (String.singleton (Char.ofNat 11) ++ "0") == none

-- Strings and the eight short escapes.
#guard document.runOption "\"\"" == some (.string "")
#guard document.runOption "\"hello, 世界\"" == some (.string "hello, 世界")
#guard document.runOption "\"line separator\"" == some (.string "line separator")
#guard document.runOption "\"\\\"\\\\\\/\\b\\f\\n\\r\\t\"" ==
  some (.string ("\"\\/" ++ String.ofList
    [Char.ofNat 8, Char.ofNat 12, '\n', '\r', '\t']))
#guard document.runOption "\"\\u0000\"" ==
  some (.string (String.singleton (Char.ofNat 0)))
#guard document.runOption "\"\\u20ac\"" == some (.string "€")
#guard document.runOption "\"\\uD834\\uDD1E\"" == some (.string "𝄞")

-- Raw controls, malformed escapes, and unpaired UTF-16 surrogates are invalid.
#guard document.runOption ("\"a" ++ String.singleton (Char.ofNat 10) ++ "b\"") == none
#guard document.runOption "\"\\x\"" == none
#guard document.runOption "\"\\u12x4\"" == none
#guard document.runOption "\"\\uD834\"" == none
#guard document.runOption "\"\\uDD1E\"" == none
#guard document.runOption "\"\\uD834\\u0041\"" == none
#guard document.runOption "\"\\uDD1E\\uD834\"" == none
#guard document.runOption "\"\\uD834\\uD834\"" == none
#guard document.runOption "\"unterminated" == none

-- Arrays, including heterogeneous and recursive values.
#guard document.runOption "[]" == some (.array [])
#guard document.runOption "[null,true,-2.5,\"x\"]" == some (.array
  [.null, .bool true, .number ⟨"-2.5"⟩, .string "x"])
#guard document.runOption "[[],[{}]]" == some (.array
  [.array [], .array [.object []]])

-- Objects preserve member order and duplicate names.
#guard document.runOption "{}" == some (.object [])
#guard document.runOption "{\"a\":1,\"b\":[false]}" == some (.object
  [("a", .number ⟨"1"⟩), ("b", .array [.bool false])])
#guard document.runOption "{\"a\":1,\"a\":2}" == some (.object
  [("a", .number ⟨"1"⟩), ("a", .number ⟨"2"⟩)])
#guard document.runOption " { \"nested\" : { \"ok\" : true } } " == some (.object
  [("nested", .object [("ok", .bool true)])])

-- Separators and delimiters are strict.
#guard document.runOption "[1,]" == none
#guard document.runOption "[,1]" == none
#guard document.runOption "[1,,2]" == none
#guard document.runOption "[1 2]" == none
#guard document.runOption "[" == none
#guard document.runOption "{\"a\":1,}" == none
#guard document.runOption "{,\"a\":1}" == none
#guard document.runOption "{\"a\" 1}" == none
#guard document.runOption "{\"a\":}" == none
#guard document.runOption "{1:true}" == none
#guard document.runOption "{" == none
