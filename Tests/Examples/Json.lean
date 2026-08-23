import Examples.Json
import Tests.Basic

open Parser Parser.Utf8 Json

#guard json.runOption "null" == some .null
#guard json.runOption "true" == some (.bool true)
#guard json.runOption "false" == some (.bool false)
#guard json.runOption "42" == some (.num 42)
#guard json.runOption "\"hello\"" == some (.str "hello")
#guard json.runOption "[]" == some (.arr [])
#guard json.runOption "[1, 2]" == some (.arr [.num 1, .num 2])
#guard json.runOption "{}" == some (.obj [])

#guard json.runOption "{\"a\": 1}"
    == some (.obj [("a", .num 1)])

#guard json.runOption "{\"x\": [1, 2], \"y\": true}"
    == some (.obj [("x", .arr [.num 1, .num 2]), ("y", .bool true)])

-- negative: empty input
#guard json.runOption "" == none

-- negative: unclosed array
#guard json.runOption "[" == none

-- negative: unclosed object
#guard json.runOption "{" == none

-- negative: unclosed string
#guard json.runOption "\"hello" == none

-- negative: misspelled keyword
#guard json.runOption "nul" == none

-- negative: bare comma
#guard json.runOption "," == none

-- negative: missing value in object
#guard json.runOption "{\"a\":}" == none

-- negative: missing colon in object
#guard json.runOption "{\"a\" 1}" == none
