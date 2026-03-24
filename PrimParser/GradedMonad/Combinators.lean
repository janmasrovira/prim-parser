import PrimParser.Base
import PrimParser.GradedMonad.Basic
import PrimParser.GradedMonad.DoNotation

variable
  {G : Type} [Monoid G]
  {M : GradedType G} [GMonad M]
  {g gl gr : G}
  {α β γ : Type}

def replicateG (x : M g α) : (n : Nat) → M (g ^ n) (List.Vector α n)
  | 0 => gdo
      return .nil
      grade_by by simp
  | n + 1 => gdo
      let h ← x
      let t ← replicateG x n
      gpure (h ::ᵥ t)
      grade_by by rw [mul_one, pow_succ']

def between' (l : M gl α) (r : M gr β) (c : M g γ) : M (gl * g * gr) (α × γ × β) := gdo
  let l' ← l
  let c' ← c
  let r' ← r
  gpure (l', c', r')
  grade_by by ac_nf

def between (l : M gl α) (r : M gr β) (c : M g γ) : M (gl * g * gr) γ := gdo
  (fun x => x.2.1) <$>ᵍ between' l r c
