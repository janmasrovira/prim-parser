import Examples.Csv
import Tests.Basic

open Parser Parser.Char Csv

-- single field
#guard row.runOption "hello" == some ["hello"]

-- multiple fields
#guard row.runOption "a,b,c" == some ["a", "b", "c"]

-- empty fields
#guard row.runOption ",a," == some ["", "a", ""]

-- quoted field
#guard row.runOption "\"hello\"" == some ["hello"]

-- quoted field with comma
#guard row.runOption "\"a,b\",c" == some ["a,b", "c"]

-- quoted field with escaped quote
#guard row.runOption "\"say \"\"hi\"\"\"" == some ["say \"hi\""]

-- negative: unclosed quote stops at empty unquoted field
#guard row.runOption "\"hello" == some [""]

-- negative: newline splits rows, not fields
#guard row.runOption "a\nb" == some ["a"]

-- negative: quote in middle of unquoted field stops parsing
#guard row.runOption "ab\"cd" == some ["ab"]

-- negative: empty input gives one empty field
#guard row.runOption "" == some [""]

-- table: basic
#guard table.runOption "name,age\nAlice,30\nBob,25"
    == some ⟨2, { columns := ⟨["name", "age"], rfl⟩,
                   rows := [⟨[.str "Alice", .int 30], rfl⟩,
                             ⟨[.str "Bob", .int 25], rfl⟩] }⟩

-- table: negative integers
#guard table.runOption "x\n-1\n-42"
    == some ⟨1, { columns := ⟨["x"], rfl⟩,
                   rows := [⟨[.int (-1)], rfl⟩, ⟨[.int (-42)], rfl⟩] }⟩

-- table: mixed values
#guard table.runOption "item,qty,note\nwidget,100,ok\ngadget,-5,\"back order\""
    == some ⟨3, { columns := ⟨["item", "qty", "note"], rfl⟩,
                   rows := [⟨[.str "widget", .int 100, .str "ok"], rfl⟩,
                             ⟨[.str "gadget", .int (-5), .str "back order"], rfl⟩] }⟩

-- table: single row
#guard table.runOption "a,b\n1,2"
    == some ⟨2, { columns := ⟨["a", "b"], rfl⟩,
                   rows := [⟨[.int 1, .int 2], rfl⟩] }⟩

-- table: quoted header
#guard table.runOption "\"col 1\",col2\n10,20"
    == some ⟨2, { columns := ⟨["col 1", "col2"], rfl⟩,
                   rows := [⟨[.int 10, .int 20], rfl⟩] }⟩

-- negative: table requires at least a header and newline
#guard table.runOption "a,b" == none

-- negative: empty input
#guard table.runOption "" == none

-- extra fields are left unconsumed: parses exactly n fields per row
#guard table.runOption "a,b\n1,2,3"
    == some ⟨2, { columns := ⟨["a", "b"], rfl⟩,
                   rows := [⟨[.int 1, .int 2], rfl⟩] }⟩

-- extra fields in second row are also left unconsumed
#guard table.runOption "a,b\n1,2\n1,2,3"
    == some ⟨2, { columns := ⟨["a", "b"], rfl⟩,
                   rows := [⟨[.int 1, .int 2], rfl⟩,
                             ⟨[.int 1, .int 2], rfl⟩] }⟩
