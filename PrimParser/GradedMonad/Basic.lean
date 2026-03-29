import Mathlib.Algebra.Group.Defs

/-!
# Graded Monads

Type classes for functors, applicatives, monads, and alternatives indexed by a
monoidal grade. Composition multiplies grades via the monoid operation.
-/

variable
  {G : Type} [Monoid G]

/-- A type family indexed by a grade and a type. -/
abbrev GradedType G := G → Type → Type

/-- Graded functor. -/
-- TODO is this class redundant?
class GFunctor (f : GradedType G) : Type 1 where
  gmap {i α β} (h : α → β) : f i α → f i β

/-- Graded applicative. -/
class GApplicative (f : GradedType G) extends GFunctor f where
  gpure {α} : α → f 1 α
  gseq {i j α β} : f i (α → β) → (Unit → f j α) → f (i * j) β

/-- Graded monad. -/
class GMonad (m : GradedType G) extends GApplicative m where
  gbind {i j α β} : m i α → (α → m j β) → m (i * j) β

/-- Graded alternative. -/
class GAlternative [AddSemigroup G] [Zero G] (f : GradedType G) extends GApplicative f where
  gempty {α} : f 0 α
  gchoice {α} {i j} : f i α → f j α → f (i + j) α

export GFunctor (gmap)
export GApplicative (gpure gseq)
export GMonad (gbind)
export GAlternative (gempty gchoice)

/-- Cast the the grade of a graded type -/
def gcast {f : GradedType G} {i j : G} {α} (h : i = j) (x : f i α) : f j α := h ▸ x

infixr:100 " <$>ᵍ " => gmap
infixl:60  " <*>ᵍ " => gseq
infixl:55  " >>=ᵍ " => gbind
infixl:30  " <|>ᵍ " => gchoice

class LawfulGFunctor (f : GradedType G) [GFunctor f] : Prop where
  gmap_id {i α} (x : f i α)
    : id <$>ᵍ x = x

  gmap_comp {i α β γ} (g : β → γ) (h : α → β) (x : f i α)
    : (g ∘ h) <$>ᵍ x = g <$>ᵍ (h <$>ᵍ x)

class LawfulGApplicative (f : GradedType G) [GApplicative f] : Prop extends LawfulGFunctor f where
  gmap_gpure {α β} (g : α → β) (x : α)
    : g <$>ᵍ (gpure x : f 1 α) = gpure (g x)

  gpure_gseq {i α β} (g : α → β) (x : f i α)
    : (gpure g <*>ᵍ fun () => x) ≍ (g <$>ᵍ x)

  gseq_gpure {i α β} (u : f i (α → β)) (x : α)
    : (u <*>ᵍ fun () => gpure x) ≍ ((· x) <$>ᵍ u)

  gseq_assoc {i j k α β γ} (u : f i (β → γ)) (v : f j (α → β)) (w : f k α)
    : ((Function.comp <$>ᵍ u <*>ᵍ fun () => v) <*>ᵍ fun () => w)
     ≍ (u <*>ᵍ fun () => (v <*>ᵍ fun () => w))

class LawfulGMonad (m : GradedType G) [GMonad m] : Prop extends LawfulGApplicative m where
  gpure_gbind {j α β} (x : α) (f : α → m j β)
    : (gpure x >>=ᵍ f) ≍ f x

  gbind_gpure {i α} (x : m i α)
    : (x >>=ᵍ gpure) ≍ x

  gbind_assoc {i j k α β γ} (x : m i α) (f : α → m j β) (g : β → m k γ)
    : (x >>=ᵍ f >>=ᵍ g) ≍ (x >>=ᵍ fun a => f a >>=ᵍ g)

class LawfulGAlternative [AddMonoid G] (f : GradedType G) [GAlternative f] : Prop extends LawfulGApplicative f where
  gempty_gchoice {i α} (x : f i α)
    : (gempty <|>ᵍ x) ≍ x

  gchoice_gempty {i α} (x : f i α)
    : (x <|>ᵍ gempty) ≍ x

  gchoice_assoc {i j k α} (x : f i α) (y : f j α) (z : f k α)
    : ((x <|>ᵍ y) <|>ᵍ z) ≍ (x <|>ᵍ (y <|>ᵍ z))

class LawfulGMonadPlus [AddMonoid G] (m : GradedType G) [GAlternative m] [GMonad m] : Prop extends LawfulGAlternative m where
  gempty_gbind {α β i} {x : α → m i β} : gempty >>=ᵍ x ≍ (gempty : m 0 β)
  gbind_gempty {α β i} {x : m i α} : x >>=ᵍ (fun _ => (gempty : m 0 β)) ≍ (gempty : m 0 β)
