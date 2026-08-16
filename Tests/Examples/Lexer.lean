import Examples.Lexer
import Tests.Basic

open Parser Parser.Char Lex

#guard lex.runOption "1+2" == some #[.num 1, .plus, .num 2]
#guard lex.runOption "  12 * ( 3 ) " == some #[.num 12, .times, .lparen, .num 3, .rparen]
#guard lex.runOption "" == some #[]

#guard (eval.runOn (Input.ofArray #[.num 7])).toOption == some 7
#guard (eval.runOn (Input.ofArray #[.num 2, .times, .num 5])).toOption == some 10

#guard run "7" == some 7
#guard run "1 + 2 * 3" == some 7
#guard run "(1 + 2) * 3" == some 9
#guard run "10 * 10 + 1" == some 101
#guard run "2 * (3 + 4) - 5" == some 9
#guard run "  42  " == some 42

#guard lex.runOption "1 +" == some #[.num 1, .plus]
#guard run "1 +" == none
#guard run "" == none
