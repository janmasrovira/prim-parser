import Mathlib.Algebra.Group.Defs

/-!
# Graded Monads

Type classes for functors, applicatives, and monads indexed by a grade. The raw
versions require only `Mul` and `One`; the `Lawful*` classes require a `Monoid`.
-/

variable
  {G : Type}

/-- A type family indexed by a grade and a type. -/
abbrev GradedType G := G → Type → Type

/-- Graded functor. -/
class GradedFunctor (f : GradedType G) : Type 1 where
  gmap {i α β} (h : α → β) : f i α → f i β

/-- Graded applicative. -/
class GradedApplicative [One G] [Mul G] (f : GradedType G) extends GradedFunctor f where
  gpure {α} : α → f 1 α
  gseq {i j α β} : f i (α → β) → (Unit → f j α) → f (i * j) β

/-- Graded monad. -/
class GradedMonad [One G] [Mul G] (m : GradedType G) extends GradedApplicative m where
  gbind {i j α β} : m i α → (α → m j β) → m (i * j) β

export GradedFunctor (gmap)
export GradedApplicative (gpure gseq)
export GradedMonad (gbind)

/-- Cast the grade of a graded type -/
def gcast {f : GradedType G} {i j : G} {α} (h : i = j) (x : f i α) : f j α := h ▸ x

/-- Replace the result of a graded computation with a constant value. -/
abbrev gconst {f : GradedType G} [GradedFunctor f] {i α β} (b : β) (x : f i α) : f i β :=
  gmap (fun _ => b) x

infixr:100 " <$>ᵍ " => gmap
infixr:100 " <$ᵍ "  => gconst
infixl:60  " <*>ᵍ " => gseq
infixl:55  " >>=ᵍ " => gbind

class LawfulGradedFunctor [Monoid G] (f : GradedType G) [GradedFunctor f] : Prop where
  gmap_id {i α} (x : f i α)
    : id <$>ᵍ x = x

  gmap_comp {i α β γ} (g : β → γ) (h : α → β) (x : f i α)
    : (g ∘ h) <$>ᵍ x = g <$>ᵍ (h <$>ᵍ x)

class LawfulGradedApplicative [Monoid G] (f : GradedType G) [GradedApplicative f] : Prop extends LawfulGradedFunctor f where
  gmap_gpure {α β} (g : α → β) (x : α)
    : g <$>ᵍ (gpure x : f 1 α) = gpure (g x)

  gpure_gseq {i α β} (g : α → β) (x : f i α)
    : (gpure g <*>ᵍ fun () => x) ≍ (g <$>ᵍ x)

  gseq_gpure {i α β} (u : f i (α → β)) (x : α)
    : (u <*>ᵍ fun () => gpure x) ≍ ((· x) <$>ᵍ u)

  gseq_assoc {i j k α β γ} (u : f i (β → γ)) (v : f j (α → β)) (w : f k α)
    : ((Function.comp <$>ᵍ u <*>ᵍ fun () => v) <*>ᵍ fun () => w)
     ≍ (u <*>ᵍ fun () => (v <*>ᵍ fun () => w))

class LawfulGradedMonad [Monoid G] (m : GradedType G) [GradedMonad m] : Prop extends LawfulGradedApplicative m where
  gpure_gbind {j α β} (x : α) (f : α → m j β)
    : (gpure x >>=ᵍ f) ≍ f x

  gbind_gpure {i α} (x : m i α)
    : (x >>=ᵍ gpure) ≍ x

  gbind_assoc {i j k α β γ} (x : m i α) (f : α → m j β) (g : β → m k γ)
    : (x >>=ᵍ f >>=ᵍ g) ≍ (x >>=ᵍ fun a => f a >>=ᵍ g)
