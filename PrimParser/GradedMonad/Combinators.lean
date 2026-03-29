import PrimParser.Base
import PrimParser.GradedMonad.Basic
import PrimParser.GradedMonad.DoNotation

variable
  {G : Type} [Monoid G]
  {M : GradedType G} [GMonad M]
  {g gl gr : G}
  {α β γ : Type}

/-- Run a graded computation `n` times, collecting results into a vector. -/
def replicateG (x : M g α) : (n : Nat) → M (g ^ n) (List.Vector α n)
  | 0 => gdo
      return .nil
      grade_by by simp
  | n + 1 => gdo
      let h ← x
      let t ← replicateG x n
      gpure (h ::ᵥ t)
      grade_by by rw [mul_one, pow_succ']

/-- Run `c` between `l` and `r`, returning all three results. -/
def between' (l : M gl α) (r : M gr β) (c : M g γ) : M (gl * g * gr) (α × γ × β) := gdo
  let l' ← l
  let c' ← c
  let r' ← r
  gpure (l', c', r')
  grade_by by ac_nf

/-- Run `c` between `l` and `r`, returning only the middle result. -/
def between (l : M gl α) (r : M gr β) (c : M g γ) : M (gl * g * gr) γ := gdo
  (fun x => x.2.1) <$>ᵍ between' l r c
