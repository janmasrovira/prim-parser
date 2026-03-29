import Examples.Csv
import Tests.Basic

open Parser Csv

-- single field
#guard row.runResult? (toText "hello") == some ["hello"]

-- multiple fields
#guard row.runResult? (toText "a,b,c") == some ["a", "b", "c"]

-- empty fields
#guard row.runResult? (toText ",a,") == some ["", "a", ""]

-- quoted field
#guard row.runResult? (toText "\"hello\"") == some ["hello"]

-- quoted field with comma
#guard row.runResult? (toText "\"a,b\",c") == some ["a,b", "c"]

-- quoted field with escaped quote
#guard row.runResult? (toText "\"say \"\"hi\"\"\"") == some ["say \"hi\""]

-- multiple rows
#guard csv.runResult? (toText "a,b\n1,2") == some [["a", "b"], ["1", "2"]]

-- three rows
#guard csv.runResult? (toText "name,age\nAlice,30\nBob,25")
    == some [["name", "age"], ["Alice", "30"], ["Bob", "25"]]

-- negative: unclosed quote stops at empty unquoted field
#guard row.runResult? (toText "\"hello") == some [""]

-- negative: newline splits rows, not fields
#guard row.runResult? (toText "a\nb") == some ["a"]

-- negative: quote in middle of unquoted field stops parsing
#guard row.runResult? (toText "ab\"cd") == some ["ab"]

-- negative: empty input gives one empty field
#guard row.runResult? (toText "") == some [""]
