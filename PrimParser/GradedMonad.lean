import Mathlib.Algebra.Group.Defs

variable
  {G : Type} [Monoid G]

abbrev GradedType G := G → Type → Type

class GFunctor (f : GradedType G) : Type 1 where
  gmap {i α β} (h : α → β) : f i α → f i β

class GApplicative (f : GradedType G) extends GFunctor f where
  gpure {α} : α → f 1 α
  gseq {i j α β} : f i (α → β) → (Unit → f j α) → f (i * j) β

class GMonad (m : GradedType G) extends GApplicative m where
  gbind {i j α β} : m i α → (α → m j β) → m (i * j) β
