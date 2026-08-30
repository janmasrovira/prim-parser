/-!
# A window of a `ByteArray`.
-/

namespace Parser

/-- A `w` bytes window of `buf[start .. start + w - 1]` -/
structure BytesWindow (w : Nat) where
  buf : ByteArray
  start : Nat
  valid : start + w ≤ buf.size

variable
  {w : Nat}

instance : GetElem (BytesWindow w) Nat UInt8 (fun _ i => i < w) where
  getElem b i h := b.buf[b.start + i]'(by have := b.valid; omega)

@[simp] theorem BytesWindow.getElem_def (b : BytesWindow w) (i : Nat) (h : i < w)
  : b[i] = b.buf[b.start + i]'(by have := b.valid; omega) := rfl

abbrev BytesWindow.narrow
  (b : BytesWindow w)
  (offset w' : Nat)
  (h : offset + w' ≤ w := by omega) : BytesWindow w' where
  buf := b.buf
  start := b.start + offset
  valid := by have := b.valid; omega

def BytesWindow.toByteArray (b : BytesWindow w) : ByteArray :=
  b.buf.extract b.start (b.start + w)

theorem BytesWindow.toByteArray_succ (b : BytesWindow (w + 1))
  : b.toByteArray = [b[0]].toByteArray ++ (b.narrow 1 w).toByteArray := by
  have := b.valid
  simp [toByteArray, getElem_def]
  rw [← ByteArray.extract_add_one (i := b.start) (by omega), ByteArray.extract_append_extract]
  congr <;> omega

end Parser
