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
