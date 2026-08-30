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

end Parser
