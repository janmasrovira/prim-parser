import PrimParser

open Parser Parser.Byte

private def bs (l : List UInt8) : ByteArray := l.toByteArray

-- take1
#guard (take1 1).runBytesOption (bs [1, 2, 3]) == some (bs [1, 2])
#guard (take1 2).runBytesOption (bs [1, 2, 3]) == some (bs [1, 2, 3])
#guard (take1 3).runBytesOption (bs [1, 2, 3]) == none

private def skipThenTake : ByteParser Error conditional ByteArray := gdo
  let _ ← uint8
  take1 1

#guard skipThenTake.runBytesOption (bs [1, 2, 3, 4]) == some (bs [2, 3])

-- takeRest
#guard takeRest.runBytesOption (bs [1, 2, 3]) == some (bs [1, 2, 3])
#guard takeRest.runBytesOption (bs []) == some .empty

private def restAfterOne : ByteParser Error conditional ByteArray := gdo
  let _ ← uint8
  takeRest

#guard restAfterOne.runBytesOption (bs [1, 2, 3]) == some (bs [2, 3])

#guard (many uint8).runBytesOption (bs [1, 2, 3]) == some [1, 2, 3]

-- unsigned integers
#guard uint8.runBytesOption (bs [0xFF]) == some 0xFF
#guard uint8.runBytesOption (bs []) == none
#guard uint16be.runBytesOption (bs [0x12, 0x34]) == some 0x1234
#guard uint16le.runBytesOption (bs [0x12, 0x34]) == some 0x3412
#guard uint16be.runBytesOption (bs [0x12]) == none
#guard uint32be.runBytesOption (bs [0x12, 0x34, 0x56, 0x78]) == some 0x12345678
#guard uint32le.runBytesOption (bs [0x12, 0x34, 0x56, 0x78]) == some 0x78563412
#guard uint32be.runBytesOption (bs [0x12, 0x34, 0x56]) == none
#guard uint64be.runBytesOption (bs [1, 2, 3, 4, 5, 6, 7, 8]) == some 0x0102030405060708
#guard uint64le.runBytesOption (bs [1, 2, 3, 4, 5, 6, 7, 8]) == some 0x0807060504030201
#guard uint64be.runBytesOption (bs [1, 2, 3, 4, 5, 6, 7]) == none

-- signed integers
#guard int8.runBytesOption (bs [0xFF]) == some (-1)
#guard int8.runBytesOption (bs [0x7F]) == some 127
#guard int16be.runBytesOption (bs [0xFF, 0xFE]) == some (-2)
#guard int16le.runBytesOption (bs [0xFE, 0xFF]) == some (-2)
#guard int32be.runBytesOption (bs [0xFF, 0xFF, 0xFF, 0xFF]) == some (-1)
#guard int32le.runBytesOption (bs [0x00, 0x00, 0x00, 0x80]) == some (-2147483648)
#guard int64be.runBytesOption (bs [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]) == some (-1)
#guard int64le.runBytesOption (bs [1, 0, 0, 0, 0, 0, 0, 0]) == some 1

-- a length-prefixed record
private def record : ByteParser Error conditional (UInt32 × ByteArray) := gdo
  let len ← uint32be
  let body ← takeRest
  return (len, body)

#guard record.runBytesOption (bs [0, 0, 0, 2, 0xAA, 0xBB]) == some (2, bs [0xAA, 0xBB])
