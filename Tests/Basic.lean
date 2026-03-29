import PrimParser

open Parser

def toText (s : String) : Text s.toList.length := ⟨s.toList, rfl⟩

-- anyChar
#guard anyChar.runResult? (toText "abc") == some 'a'
#guard anyChar.runResult? (toText "") == none

-- char
#guard (char 'a').runResult? (toText "abc") == some ()
#guard (char 'x').runResult? (toText "abc") == none

-- satisfy
#guard (satisfy Char.isAlpha).runResult? (toText "abc") == some 'a'
#guard (satisfy Char.isDigit).runResult? (toText "x") == none

-- string
#guard (string "hel").runResult? (toText "hello") == some ()
#guard (string "xyz").runResult? (toText "hello") == none

-- many
#guard (many (satisfy Char.isDigit)).runResult? (toText "x") == some []
#guard (many (satisfy Char.isDigit)).runResult? (toText "123x") == some ['1', '2', '3']

-- optional
#guard (optional (satisfy Char.isDigit)).runResult? (toText "1x") == some (some '1')
#guard (optional (satisfy Char.isDigit)).runResult? (toText "x") == some none

-- many1
#guard (many1 (satisfy Char.isDigit)).runResult? (toText "123x") == some ['1', '2', '3']
#guard (many1 (satisfy Char.isDigit)).runResult? (toText "x") == none

-- sepBy
#guard (sepBy (string ",") (satisfy Char.isAlpha)).runResult? (toText "a,b,c")
    == some ['a', 'b', 'c']
#guard (sepBy (string ",") (satisfy Char.isAlpha)).runResult? (toText "123")
    == some []

-- digit
#guard digit.runResult? (toText "7x") == some 7
#guard digit.runResult? (toText "x") == none

-- nat
#guard nat.runResult? (toText "0") == some 0
#guard nat.runResult? (toText "42x") == some 42
#guard nat.runResult? (toText "123") == some 123
#guard nat.runResult? (toText "x") == none

-- chainl1
private def plus : Parser Error .conditional (Nat → Nat → Nat) := gdo
  let _ ← satisfy (· == '+')
  return (· + ·)

#guard (chainl1 plus digit).runResult? (toText "5") == some 5
#guard (chainl1 plus digit).runResult? (toText "1+2+3") == some 6

-- eof
#guard eof.runResult? (toText "") == some ()
#guard eof.runResult? (toText "x") == none

-- takeWhile / takeWhile1
#guard (takeWhile Char.isAlpha).runResult? (toText "abc123") == some "abc"
#guard (takeWhile Char.isAlpha).runResult? (toText "123") == some ""
#guard (takeWhile1 Char.isAlpha).runResult? (toText "abc123") == some "abc"
#guard (takeWhile1 Char.isAlpha).runResult? (toText "123") == none

-- skipWhile / skipWhile1
#guard (gdo skipWhile Char.isWhitespace; nat).runResult? (toText "  42") == some 42
#guard (gdo skipWhile Char.isWhitespace; nat).runResult? (toText "42") == some 42
#guard (gdo skipWhile1 Char.isWhitespace; nat).runResult? (toText " 42") == some 42
#guard (gdo skipWhile1 Char.isWhitespace; nat).runResult? (toText "42") == none

-- whitespace / lexeme
#guard (gdo whitespace; nat).runResult? (toText "  42") == some 42
#guard (lexeme nat).runResult? (toText "42  ") == some 42

-- lookahead
#guard (gdo let _ ← lookahead nat; nat).runResult? (toText "42") == some 42
#guard (lookahead nat).runResult? (toText "x") == none

-- notFollowedBy
#guard (gdo notFollowedBy (char 'x'); nat).runResult? (toText "42") == some 42
#guard (gdo notFollowedBy (char 'x'); nat).runResult? (toText "x2") == none

-- manyTill
#guard (manyTill anyChar (char '.')).runResult? (toText "abc.") == some ['a', 'b', 'c']
#guard (manyTill anyChar (char '.')).runResult? (toText ".") == some []

-- withRecovery
private def recoverDigit : Error → Parser Error .conditional Nat :=
  fun _ => digit

#guard (withRecovery recoverDigit (char 'x' >>=ᵍ fun _ => gpure 99)).runResult? (toText "x")
    == some 99
#guard (withRecovery recoverDigit (char 'x' >>=ᵍ fun _ => gpure 99)).runResult? (toText "5")
    == some 5
