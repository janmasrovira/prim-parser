import Examples.Json
import Tests.Basic

open Parser Parser.Utf8 Json

#guard Json.json.runOption "null" == some .null
#guard Json.json.runOption "true" == some (.bool true)
#guard Json.json.runOption "false" == some (.bool false)
#guard Json.json.runOption "42" == some (.num 42)
#guard Json.json.runOption "\"hello\"" == some (.str "hello")
#guard Json.json.runOption "[]" == some (.arr [])
#guard Json.json.runOption "[1, 2]" == some (.arr [.num 1, .num 2])
#guard Json.json.runOption "{}" == some (.obj [])

#guard Json.json.runOption "{\"a\": 1}"
    == some (.obj [("a", .num 1)])

#guard Json.json.runOption "{\"x\": [1, 2], \"y\": true}"
    == some (.obj [("x", .arr [.num 1, .num 2]), ("y", .bool true)])

-- negative: empty input
#guard Json.json.runOption "" == none

-- negative: unclosed array
#guard Json.json.runOption "[" == none

-- negative: unclosed object
#guard Json.json.runOption "{" == none

-- negative: unclosed string
#guard Json.json.runOption "\"hello" == none

-- negative: misspelled keyword
#guard Json.json.runOption "nul" == none

-- negative: bare comma
#guard Json.json.runOption "," == none

-- negative: missing value in object
#guard Json.json.runOption "{\"a\":}" == none

-- negative: missing colon in object
#guard Json.json.runOption "{\"a\" 1}" == none
