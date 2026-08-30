import Mathlib.Order.Fin.Basic

class Buffer (σ : Type) where
  size : σ → Nat

namespace Buffer

variable {σ : Type} [Buffer σ]

instance : Buffer ByteArray where
  size := ByteArray.size

@[simp] theorem size_byteArray (b : ByteArray) : size b = b.size := rfl

instance {τ : Type} : Buffer (Array τ) where
  size := Array.size

@[simp] theorem size_array {τ : Type} (a : Array τ) : size a = a.size := rfl

end Buffer
