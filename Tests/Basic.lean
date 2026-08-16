import PrimParser

open Parser Parser.Char

#guard anyChar.runOption "abc" == some 'a'
#guard anyChar.runOption "" == none
#guard anyChar.runOption "é" == some 'é'
#guard anyChar.runOption "😀" == some '😀'

#guard anyByte.runOption "é" == some 0xC3
#guard anyByte.runOption "A" == some 0x41
#guard anyByte.runOption "" == none

-- char
#guard (char 'a').runOption "abc" == some ()
#guard (char 'x').runOption "abc" == none

-- satisfy
#guard (satisfy Char.isAlpha).runOption "abc" == some 'a'
#guard (satisfy Char.isDigit).runOption "x" == none

-- string
#guard (string "hel").runOption "hello" == some ()
#guard (string "xyz").runOption "hello" == none

-- many
#guard (many (satisfy Char.isDigit)).runOption "x" == some []
#guard (many (satisfy Char.isDigit)).runOption "123x" == some ['1', '2', '3']

-- optional
#guard (optional (satisfy Char.isDigit)).runOption "1x" == some (some '1')
#guard (optional (satisfy Char.isDigit)).runOption "x" == some none

-- many1
#guard (many1 (satisfy Char.isDigit)).runOption "123x" == some ('1' ::₁ ['2', '3'])
#guard (many1 (satisfy Char.isDigit)).runOption "x" == none

-- sepBy
#guard (sepBy (string ",") (satisfy Char.isAlpha)).runOption "a,b,c"
    == some ['a', 'b', 'c']
#guard (sepBy (string ",") (satisfy Char.isAlpha)).runOption "123"
    == some []

-- sepBy1
#guard (sepBy1 (string ",") (satisfy Char.isAlpha)).runOption "a,b,c"
    == some ('a' ::₁ ['b', 'c'])
#guard (sepBy1 (string ",") (satisfy Char.isAlpha)).runOption "1" == none

-- endBy
#guard (endBy (string ",") (satisfy Char.isAlpha)).runOption "a,b,"
    == some ['a', 'b']
#guard (endBy (string ",") (satisfy Char.isAlpha)).runOption "1" == some []

-- endBy1
#guard (endBy1 (string ",") (satisfy Char.isAlpha)).runOption "a,b,"
    == some ('a' ::₁ ['b'])
#guard (endBy1 (string ",") (satisfy Char.isAlpha)).runOption "a" == none

-- sepEndBy
#guard (sepEndBy (string ",") (satisfy Char.isAlpha)).runOption "a,b,c,"
    == some ['a', 'b', 'c']
#guard (sepEndBy (string ",") (satisfy Char.isAlpha)).runOption "a,b,c"
    == some ['a', 'b', 'c']

-- sepEndBy1
#guard (sepEndBy1 (string ",") (satisfy Char.isAlpha)).runOption "a,b,"
    == some ('a' ::₁ ['b'])
#guard (sepEndBy1 (string ",") (satisfy Char.isAlpha)).runOption "1" == none

-- sepByN
#guard (sepByN (string ",") (satisfy Char.isAlpha) 3).runOption "a,b,c"
    == some ⟨['a', 'b', 'c'], rfl⟩
#guard (sepByN (string ",") (satisfy Char.isAlpha) 0).runOption "abc"
    == some ⟨[], rfl⟩
#guard (sepByN (string ",") (satisfy Char.isAlpha) 2).runOption "a,b,c"
    == some ⟨['a', 'b'], rfl⟩
#guard (sepByN (string ",") (satisfy Char.isAlpha) 3).runOption "a,b" == none

-- digit
#guard digit.runOption "7x" == some 7
#guard digit.runOption "x" == none

-- ASCII.octDigit
#guard ASCII.octDigit.runOption "7x" == some 7
#guard ASCII.octDigit.runOption "8" == none

-- ASCII.hexDigit
#guard ASCII.hexDigit.runOption "9" == some 9
#guard ASCII.hexDigit.runOption "a" == some 10
#guard ASCII.hexDigit.runOption "F" == some 15
#guard ASCII.hexDigit.runOption "g" == none

-- nat
#guard nat.runOption "0" == some 0
#guard nat.runOption "42x" == some 42
#guard nat.runOption "123" == some 123
#guard nat.runOption "x" == none

-- int
#guard int.runOption "42" == some 42
#guard int.runOption "-7" == some (-7)
#guard int.runOption "-0" == some 0
#guard int.runOption "x" == none
#guard int.runOption "-x" == none

-- chainl1
private def plus : StringParser conditional (Nat → Nat → Nat) := gdo
  let _ ← satisfy (· == '+')
  return (· + ·)

#guard (chainl1 plus digit).runOption "5" == some 5
#guard (chainl1 plus digit).runOption "1+2+3" == some 6

-- eof
#guard eof.runOption "" == some ()
#guard eof.runOption "x" == none

-- takeWhile / takeWhile1
#guard (takeWhile Char.isAlpha).runOption "abc123" == some "abc"
#guard (takeWhile Char.isAlpha).runOption "123" == some ""
#guard (takeWhile1 Char.isAlpha).runOption "abc123" == some "abc"
#guard (takeWhile1 Char.isAlpha).runOption "123" == none

-- skipWhile / skipWhile1
#guard (gdo skipWhile Char.isWhitespace; nat).runOption "  42" == some 42
#guard (gdo skipWhile Char.isWhitespace; nat).runOption "42" == some 42
#guard (gdo skipWhile1 Char.isWhitespace; nat).runOption " 42" == some 42
#guard (gdo skipWhile1 Char.isWhitespace; nat).runOption "42" == none

-- skip
#guard (skip 3 (satisfy Char.isDigit)).runOption "123abc" == some ()
#guard (skip 3 (satisfy Char.isDigit)).runOption "12" == none

-- skipUpTo
#guard (skipUpTo 5 (satisfy Char.isDigit)).runOption "12abc" == some ()
#guard (skipUpTo 0 (satisfy Char.isDigit)).runOption "abc" == some ()

-- skipManyN
#guard (skipManyN 2 (satisfy Char.isDigit)).runOption "1234abc" == some ()
#guard (skipManyN 2 (satisfy Char.isDigit)).runOption "1abc" == none

-- skipUntil
#guard (skipUntil (string ";") (satisfy Char.isAlpha)).runOption "abc;rest" == some ()
#guard (skipUntil (string ";") (satisfy Char.isAlpha)).runOption "abc" == none

-- whitespace / lexeme
#guard (gdo whitespace; nat).runOption "  42" == some 42
#guard (lexeme nat).runOption "42  " == some 42

-- lookahead
#guard (gdo let _ ← lookahead nat; nat).runOption "42" == some 42
#guard (lookahead nat).runOption "x" == none

-- notFollowedBy
#guard (gdo notFollowedBy (char 'x'); nat).runOption "42" == some 42
#guard (gdo notFollowedBy (char 'x'); nat).runOption "x2" == none

-- manyTill
#guard (manyTill anyChar (char '.')).runOption "abc." == some ['a', 'b', 'c']
#guard (manyTill anyChar (char '.')).runOption "." == some []

-- withRecovery
private def recoverDigit : Error → StringParser conditional Nat :=
  fun _ => digit

#guard (withRecovery recoverDigit (char 'x' >>=ᵍ fun _ => gpure 99)).runOption "x"
    == some 99
#guard (withRecovery recoverDigit (char 'x' >>=ᵍ fun _ => gpure 99)).runOption "5"
    == some 5

-- tryResume
private def alwaysFail : StringParser conditional Char := satisfy (fun _ => false)
#guard (tryResume alwaysFail anyChar).runOption "abc" == some 'b'
#guard (tryResume (withBacktracking alwaysFail) anyChar).runOption "abc" == some 'a'

-- choice
#guard (alwaysFail <|> anyChar).runOption "abc" == some 'a'
