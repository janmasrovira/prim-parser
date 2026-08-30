import PrimParser.Basic
import PrimParser.BytesWindow

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

private theorem pos_add_le {m : Nat} (t : Input ByteArray UInt8 n) (h : m + 1 ≤ n)
  : t.pos + m + 1 ≤ t.buf.size := by
  have := t.valid; simp only [Input.pos, size_uint8] at *; omega

/-- Consume exactly `k + 1` bytes and decode them in place. -/
@[inline] private def withTake1
  (k : Nat)
  (decode : BytesWindow (k + 1) → α)
  : ByteParser Error conditional α where
  run {n} t :=
    if h : k + 1 ≤ n then
      success { result := decode { buf := t.buf, start := t.pos, valid := pos_add_le t h }
                restSize := n - (k + 1) }
    else
      failure { error := Error.eof, restSize := 0 }

/-- Consume all remaining input. -/
def takeRest : ByteParser Error flexible ByteArray :=
  List.toByteArray <$>ᵍ many anyTok

private def takeRestImpl : ByteParser Error flexible ByteArray where
  run {n} t :=
    success { result := t.buf.extract t.pos t.buf.size
              restSize := 0 }

private theorem nextTok_eq
  (t : Input ByteArray UInt8 (n + 1))
  (h : t.pos < t.buf.size := by simpa using t.pos_lt)
  : t.nextTok = some t.buf[t.pos] := by simp [Input.pos]

theorem many_go_anyTok_restSize
  (t : Input ByteArray UInt8 n)
  : (many.go anyTok t).restSize = 0 := by
  induction n <;> rw [many.go]
  case zero => rw [anyTok_run_eof]
  case succ n ih => rw [anyTok_run_some (nextTok_eq t), ih]

theorem many_go_anyTok_result
  (t : Input ByteArray UInt8 n)
  : (many.go anyTok t).result = t.buf.data.toList.drop t.pos := by
  induction n <;> rw [many.go]
  case zero => simp [anyTok_run_eof, Input.pos]
  case succ n ih =>
    simp [anyTok_run_some (nextTok_eq t), ih, ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]

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

variable {β γ : Type}

section

variable
  {k : Nat}
  {decode : BytesWindow (k + 1) → α}

private theorem withTake1_run_success
  {t : Input ByteArray UInt8 n}
  (h : k + 1 ≤ n := by assumption)
  (hp : t.pos + (k + 1) ≤ t.buf.size := by exact pos_add_le _ (by omega))
  : (withTake1 k decode).run t
    = success { result := decode { buf := t.buf, start := t.pos, valid := hp }
                restSize := n - (k + 1) } := by
  simp [withTake1, h]

private theorem withTake1_run_eof
  {t : Input ByteArray UInt8 n}
  (h : ¬ k + 1 ≤ n := by assumption)
  : (withTake1 k decode).run t = failure { error := Error.eof, restSize := 0 } := by
  simp [withTake1, h]

end

private theorem gpure_run (a : α) (t : Input ByteArray UInt8 n)
  : (gpure a : ByteParser Error 1 α).run t = success { result := a, restSize := n } := rfl

private theorem anyTok_eq_withTake1
  : anyTok = withTake1 0 (fun b => b[0]) := by
  ext n t
  cases n with
  | zero => simp [withTake1, anyTok_run_eof]
  | succ n => simp [withTake1, anyTok_run_some (nextTok_eq t)]

/-- Two adjacent reads are one read of the combined width. -/
private theorem withTake1_bind {j k : Nat}
  (decodeFst : BytesWindow (j + 1) → α)
  (decodeSnd : BytesWindow (k + 1) → β)
  (combine : α → β → γ)
  : (gdo
      let x ← withTake1 j decodeFst
      let y ← withTake1 k decodeSnd
      return combine x y)
    = withTake1 (j + k + 1) fun b =>
        combine (decodeFst (b.narrow 0 (j + 1))) (decodeSnd (b.narrow (j + 1) (k + 1))) := by
  ext n t
  simp only [gbind_run, Success.bindParser]
  by_cases hj : j + 1 ≤ n
  case neg =>
    rw [Outcome.handle_failure withTake1_run_eof,
        withTake1_run_eof (k := j + k + 1) (by omega)]
  case pos =>
    rw [Outcome.handle_success withTake1_run_success]
    by_cases hk : k + 1 ≤ n - (j + 1)
    case neg =>
      rw [Outcome.handle_failure withTake1_run_eof,
          withTake1_run_eof (k := j + k + 1) (by omega)]
      rfl
    case pos =>
      have hpos : (t.dropTo (n - (j + 1))).pos = t.pos + j + 1 := by
        simp only [Input.pos_dropTo]; omega
      have hrest : n - (j + 1) - (k + 1) = n - (j + k + 2) := by omega
      rw [Outcome.handle_success withTake1_run_success,
          withTake1_run_success (k := j + k + 1) (by omega)]
      simp only [gpure_run, Success.seq, Input.dropTo_buf, hpos, hrest]
      rfl

private theorem withTake1_gmap {k : Nat}
  (decode : BytesWindow (k + 1) → α)
  (f : α → β)
  : (f <$>ᵍ withTake1 k decode) = withTake1 k (fun b => f (decode b)) := by
  ext n t
  simp only [gmap_run, withTake1]
  split <;> rfl

private abbrev be16 (b : BytesWindow 2) : UInt16 :=
  b[0].toUInt16 <<< 8 ||| b[1].toUInt16

private abbrev le16 (b : BytesWindow 2) : UInt16 :=
  b[1].toUInt16 <<< 8 ||| b[0].toUInt16

private abbrev be32 (b : BytesWindow 4) : UInt32 :=
  (be16 (b.narrow 0 2)).toUInt32 <<< 16 ||| (be16 (b.narrow 2 2)).toUInt32

private abbrev le32 (b : BytesWindow 4) : UInt32 :=
  (le16 (b.narrow 2 2)).toUInt32 <<< 16 ||| (le16 (b.narrow 0 2)).toUInt32

private abbrev be64 (b : BytesWindow 8) : UInt64 :=
  (be32 (b.narrow 0 4)).toUInt64 <<< 32 ||| (be32 (b.narrow 4 4)).toUInt64

private abbrev le64 (b : BytesWindow 8) : UInt64 :=
  (le32 (b.narrow 4 4)).toUInt64 <<< 32 ||| (le32 (b.narrow 0 4)).toUInt64

private def uint16beImpl : ByteParser Error conditional UInt16 :=
  withTake1 1 be16

@[csimp] private theorem uint16be_eq_impl : @uint16be = @uint16beImpl := by
  rw [uint16be, uint16beImpl, uint8, anyTok_eq_withTake1, withTake1_bind]
  rfl

private def uint16leImpl : ByteParser Error conditional UInt16 :=
  withTake1 1 le16

@[csimp] private theorem uint16le_eq_impl : @uint16le = @uint16leImpl := by
  rw [uint16le, uint16leImpl, uint8, anyTok_eq_withTake1, withTake1_bind]
  rfl

private def uint32beImpl : ByteParser Error conditional UInt32 :=
  withTake1 3 be32

@[csimp] private theorem uint32be_eq_impl : @uint32be = @uint32beImpl := by
  rw [uint32be, uint32beImpl, uint16be_eq_impl, uint16beImpl, withTake1_bind]

private def uint32leImpl : ByteParser Error conditional UInt32 :=
  withTake1 3 le32

@[csimp] private theorem uint32le_eq_impl : @uint32le = @uint32leImpl := by
  rw [uint32le, uint32leImpl, uint16le_eq_impl, uint16leImpl, withTake1_bind]

private def uint64beImpl : ByteParser Error conditional UInt64 :=
  withTake1 7 be64

@[csimp] private theorem uint64be_eq_impl : @uint64be = @uint64beImpl := by
  rw [uint64be, uint64beImpl, uint32be_eq_impl, uint32beImpl, withTake1_bind]

private def uint64leImpl : ByteParser Error conditional UInt64 :=
  withTake1 7 le64

@[csimp] private theorem uint64le_eq_impl : @uint64le = @uint64leImpl := by
  rw [uint64le, uint64leImpl, uint32le_eq_impl, uint32leImpl, withTake1_bind]

private def int16beImpl : ByteParser Error conditional Int16 :=
  withTake1 1 fun b => (be16 b).toInt16

@[csimp] private theorem int16be_eq_impl : @int16be = @int16beImpl := by
  rw [int16be, int16beImpl, uint16be_eq_impl, uint16beImpl, withTake1_gmap]

private def int16leImpl : ByteParser Error conditional Int16 :=
  withTake1 1 fun b => (le16 b).toInt16

@[csimp] private theorem int16le_eq_impl : @int16le = @int16leImpl := by
  rw [int16le, int16leImpl, uint16le_eq_impl, uint16leImpl, withTake1_gmap]

private def int32beImpl : ByteParser Error conditional Int32 :=
  withTake1 3 fun b => (be32 b).toInt32

@[csimp] private theorem int32be_eq_impl : @int32be = @int32beImpl := by
  rw [int32be, int32beImpl, uint32be_eq_impl, uint32beImpl, withTake1_gmap]

private def int32leImpl : ByteParser Error conditional Int32 :=
  withTake1 3 fun b => (le32 b).toInt32

@[csimp] private theorem int32le_eq_impl : @int32le = @int32leImpl := by
  rw [int32le, int32leImpl, uint32le_eq_impl, uint32leImpl, withTake1_gmap]

private def int64beImpl : ByteParser Error conditional Int64 :=
  withTake1 7 fun b => (be64 b).toInt64

@[csimp] private theorem int64be_eq_impl : @int64be = @int64beImpl := by
  rw [int64be, int64beImpl, uint64be_eq_impl, uint64beImpl, withTake1_gmap]

private def int64leImpl : ByteParser Error conditional Int64 :=
  withTake1 7 fun b => (le64 b).toInt64

@[csimp] private theorem int64le_eq_impl : @int64le = @int64leImpl := by
  rw [int64le, int64leImpl, uint64le_eq_impl, uint64leImpl, withTake1_gmap]

end Byte

end Parser
