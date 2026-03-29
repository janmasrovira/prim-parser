import Examples.Json
import Tests.Basic

open Parser Json

#guard json.runResult? (toText "null") == some .null
#guard json.runResult? (toText "true") == some (.bool true)
#guard json.runResult? (toText "false") == some (.bool false)
#guard json.runResult? (toText "42") == some (.num 42)
#guard json.runResult? (toText "\"hello\"") == some (.str "hello")
#guard json.runResult? (toText "[]") == some (.arr [])
#guard json.runResult? (toText "[1, 2]") == some (.arr [.num 1, .num 2])
#guard json.runResult? (toText "{}") == some (.obj [])

#guard json.runResult? (toText "{\"a\": 1}")
    == some (.obj [("a", .num 1)])

#guard json.runResult? (toText "{\"x\": [1, 2], \"y\": true}")
    == some (.obj [("x", .arr [.num 1, .num 2]), ("y", .bool true)])

-- negative: empty input
#guard json.runResult? (toText "") == none

-- negative: unclosed array
#guard json.runResult? (toText "[") == none

-- negative: unclosed object
#guard json.runResult? (toText "{") == none

-- negative: unclosed string
#guard json.runResult? (toText "\"hello") == none

-- negative: misspelled keyword
#guard json.runResult? (toText "nul") == none

-- negative: bare comma
#guard json.runResult? (toText ",") == none

-- negative: missing value in object
#guard json.runResult? (toText "{\"a\":}") == none

-- negative: missing colon in object
#guard json.runResult? (toText "{\"a\" 1}") == none
