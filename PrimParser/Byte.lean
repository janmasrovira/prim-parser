import PrimParser.Basic

open Buffer

/-!
# Byte parsers
-/

namespace Parser

abbrev ByteParser (ε : Type) (g : Grade) (α : Type) : Type := Parser ByteArray UInt8 ε g α

variable
  {α ε : Type}
  {n : Nat}
  {g : Grade}
  {ge gc : Necessity}

def runBytes (p : ByteParser ε g α) (b : ByteArray) : Except ε α :=
  p.runOn (Input.ofByteArray b)

def runBytesOption (p : ByteParser ε ⟨ge, gc⟩ α) (b : ByteArray) : Option α :=
  (p.runBytes b).toOption

namespace Byte

-- TODO csimp
/-- Consume exactly `k + 1` bytes. -/
def take1 (k : Nat) : ByteParser Error conditional ByteArray where
  run {n} t :=
    if h : k < n then
      success { result := t.buf.extract t.pos (t.pos + k + 1)
                restSize := n - (k + 1) }
    else
      failure { error := Error.eof
                restSize := n }

/-- Consume all remaining input. -/
def takeRest : ByteParser Error flexible ByteArray :=
  List.toByteArray <$>ᵍ many anyTok

private def takeRestImpl : ByteParser Error flexible ByteArray where
  run {n} t :=
    success { result := t.buf.extract t.pos t.buf.size
              restSize := 0 }

private theorem nextTok_eq (t : Input ByteArray UInt8 (n + 1))
  (h : t.pos < t.buf.size := by have := t.valid; simp only [Input.pos, size_uint8] at this ⊢; omega)
  : t.nextTok = some t.buf[t.pos] := by simp [Input.pos]

theorem many_go_anyTok_restSize (n : Nat)
  : ∀ t : Input ByteArray UInt8 n, (many.go anyTok t).restSize = 0 := by
  induction n with
  | zero => intro t; rw [many.go, anyTok_run_eof]
  | succ n ih => intro t; rw [many.go, anyTok_run_some (nextTok_eq t)]; exact ih _

theorem many_go_anyTok_result (n : Nat)
  : ∀ t : Input ByteArray UInt8 n, (many.go anyTok t).result = t.buf.data.toList.drop t.pos := by
  induction n with
  | zero => intro t; rw [many.go, anyTok_run_eof]; simp [Input.pos]
  | succ n ih =>
    intro t
    have hv : n + 1 ≤ t.buf.size := by simpa using t.valid
    rw [many.go, anyTok_run_some (nextTok_eq t)]
    simp only [ih, Input.dropTo, width_uint8, Input.pos, ByteArray.getElem_eq_getElem_data,
      ← Array.getElem_toList, show t.buf.size - n = t.buf.size - (n + 1) + 1 by omega,
      List.getElem_cons_drop]

@[csimp] private theorem takeRest_eq_impl : @takeRest = @takeRestImpl := by
  ext n t
  simp [takeRest, takeRestImpl, many, GradedFunctor.gmap, Functor.map,
        many_go_anyTok_result, many_go_anyTok_restSize, ByteArray.ext_iff, List.toArray_drop]

/-- Read an unsigned 8-bit integer. -/
abbrev uint8 : ByteParser Error conditional UInt8 := anyTok

/-- Read a signed 8-bit integer. -/
def int8 : ByteParser Error conditional Int8 := (·.toInt8) <$>ᵍ uint8

/-- Read a big-endian unsigned 16-bit integer. -/
def uint16be : ByteParser Error conditional UInt16 := gdo
  let hi ← uint8
  let lo ← uint8
  return hi.toUInt16 <<< 8 ||| lo.toUInt16

/-- Read a little-endian unsigned 16-bit integer. -/
def uint16le : ByteParser Error conditional UInt16 := gdo
  let lo ← uint8
  let hi ← uint8
  return hi.toUInt16 <<< 8 ||| lo.toUInt16

/-- Read a big-endian unsigned 32-bit integer. -/
def uint32be : ByteParser Error conditional UInt32 := gdo
  let hi ← uint16be
  let lo ← uint16be
  return hi.toUInt32 <<< 16 ||| lo.toUInt32

/-- Read a little-endian unsigned 32-bit integer. -/
def uint32le : ByteParser Error conditional UInt32 := gdo
  let lo ← uint16le
  let hi ← uint16le
  return hi.toUInt32 <<< 16 ||| lo.toUInt32

/-- Read a big-endian unsigned 64-bit integer. -/
def uint64be : ByteParser Error conditional UInt64 := gdo
  let hi ← uint32be
  let lo ← uint32be
  return hi.toUInt64 <<< 32 ||| lo.toUInt64

/-- Read a little-endian unsigned 64-bit integer. -/
def uint64le : ByteParser Error conditional UInt64 := gdo
  let lo ← uint32le
  let hi ← uint32le
  return hi.toUInt64 <<< 32 ||| lo.toUInt64

/-- Read a big-endian signed 16-bit integer. -/
def int16be : ByteParser Error conditional Int16 := (·.toInt16) <$>ᵍ uint16be

/-- Read a little-endian signed 16-bit integer. -/
def int16le : ByteParser Error conditional Int16 := (·.toInt16) <$>ᵍ uint16le

/-- Read a big-endian signed 32-bit integer. -/
def int32be : ByteParser Error conditional Int32 := (·.toInt32) <$>ᵍ uint32be

/-- Read a little-endian signed 32-bit integer. -/
def int32le : ByteParser Error conditional Int32 := (·.toInt32) <$>ᵍ uint32le

/-- Read a big-endian signed 64-bit integer. -/
def int64be : ByteParser Error conditional Int64 := (·.toInt64) <$>ᵍ uint64be

/-- Read a little-endian signed 64-bit integer. -/
def int64le : ByteParser Error conditional Int64 := (·.toInt64) <$>ᵍ uint64le

end Byte

end Parser
