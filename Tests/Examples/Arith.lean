import Examples.Arith
import Tests.Basic

open Parser Expr

private def eval? (s : String) : Option Int :=
  (expr.runResult? (toText s)).map Expr.eval

-- literals
#guard eval? "42" == some 42
#guard eval? "0" == some 0

-- single operations
#guard eval? "1+2" == some 3
#guard eval? "3*4" == some 12

-- left associativity
#guard eval? "1-2-3" == some (-4)

-- precedence
#guard eval? "1+2*3" == some 7
#guard eval? "2*3+4" == some 10

-- parentheses
#guard eval? "(1+2)*3" == some 9

-- whitespace
#guard eval? "(1 + 2 ) *3 " == some 9

-- nested parentheses
#guard eval? "((1+2))" == some 3

-- division
#guard eval? "10/3" == some 3
#guard eval? "10/2+1" == some 6
