import PrimParser.Basic

/-!
# PrimParser Lawfulness Proofs

Lawful instances for `Success`, `Outcome`, and `Parser`:
`LawfulFunctor`, `LawfulGradedFunctor`, `LawfulGradedApplicative`, `LawfulGradedMonad`.
-/

namespace Parser

variable
  {σ τ : Type} [Buffer σ τ]
  {α β γ ε : Type}
  {n m : Nat}
  {g g' : Grade}
  {ge gc c1 c2 : Necessity}

instance : LawfulFunctor (Success n gc) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

instance : LawfulFunctor (Outcome ε n gc) where
  map_const := rfl
  id_map x := by cases x <;> rfl
  comp_map f h x := by cases x <;> rfl

instance : LawfulGradedFunctor (Success n) where
  gmap_id _ := rfl
  gmap_comp _ _ _ := rfl

instance : LawfulGradedFunctor (Parser σ τ ε) where
  gmap_id x := by ext m t; exact id_map (x.run t)
  gmap_comp g h x := by ext m t; exact comp_map h g (x.run t)

theorem heq
  {g1 g2 : Grade}
  {p : Parser σ τ ε g1 α}
  {q : Parser σ τ ε g2 α}
  (hg : g1 = g2)
  (h : ∀ {m} (t : Input σ τ m), p.run t ≍ q.run t)
  : p ≍ q := by
  subst hg; apply heq_of_eq; ext m t; exact eq_of_heq (h t)

@[simp] theorem Failure.trans_self
  (e : Failure n ε)
  (h : n ≤ n)
  : e.trans h = e := by
  cases e; rfl

theorem Success.heq
  {s1 : Success n c1 α}
  {s2 : Success n c2 α}
  (hc : c1 = c2)
  (hr : s1.result = s2.result := by rfl)
  (hrs : s1.restSize = s2.restSize := by rfl)
  : s1 ≍ s2 := by
  subst hc; apply heq_of_eq; cases s1; cases s2; simp_all

theorem Success.seq_assoc
  {gc' gc'' : Necessity}
  {a : Success n gc α}
  {b : Success a.restSize gc' β}
  {c : Success b.restSize gc'' γ}
  : (a.seq b).seq c ≍ a.seq (b.seq c) :=
  Success.heq (sup_assoc _ _ _)

@[simp] theorem Success.seq_result
  {gc' : Necessity}
  (a : Success n gc α)
  (b : Success a.restSize gc' β)
  : (a.seq b).result = b.result := rfl

@[simp] theorem Success.seq_restSize
  {gc' : Necessity}
  (a : Success n gc α)
  (b : Success a.restSize gc' β)
  : (a.seq b).restSize = b.restSize := rfl

theorem Outcome.failure_congr
  {f : Failure n ε}
  (hc : c1 = c2)
  : (failure f : Outcome ε n c1 α) ≍ (failure f : Outcome ε n c2 α) := by
  subst hc; rfl

theorem Outcome.success_congr
  {s1 : Success n c1 α}
  {s2 : Success n c2 α}
  (hc : c1 = c2)
  (hs : s1 ≍ s2)
  : (success s1 : Outcome ε n c1 α) ≍ (success s2 : Outcome ε n c2 α) := by
  subst hc; rw [eq_of_heq hs]

theorem bind_run
  (m : Parser σ τ ε g α)
  (f : α → Parser σ τ ε g' β)
  (t : Input σ τ n)
  : (bind m f).run t
      = match m.run t with
        | failure e => failure e
        | success x => match f x.result |>.run (t.dropTo x.restSize x.le) with
          | failure e => failure (e.trans x.le)
          | success y => success (x.seq y) := by
  cases hm : m.run t with
  | failure e =>
    simp [hm, bind, Parser.handle]
    simp only [Outcome.handle]
  | success x =>
    simp only [bind, Parser.handle, hm]
    simp only [Outcome.handle, Success.bindParser]
    cases f x.result |>.run (t.dropTo x.restSize x.le) <;> rfl

theorem gpure_gbind
  {j : Grade}
  (a : α)
  (f : α → Parser σ τ ε j β)
  : (gpure a >>=ᵍ f) ≍ f a := by
  apply Parser.heq (one_mul j)
  intro m t
  simp only [gbind, gpure, bind_run, Input.dropTo_self]
  cases f a |>.run t with
  | failure e => rfl
  | success y => cases y; rfl

theorem gbind_gpure {i : Grade} (p : Parser σ τ ε i α) : (p >>=ᵍ gpure) ≍ p := by
  have hc := congrArg Grade.consumes (mul_one i)
  apply Parser.heq (mul_one i)
  intro m t
  obtain ⟨pr, ps⟩ := p
  simp only [gbind, gpure, bind_run]
  exact match pr t with
  | failure e => Outcome.failure_congr hc
  | success x => Outcome.success_congr hc (Success.heq hc)

theorem gbind_assoc
  {i j k : Grade}
  (x : Parser σ τ ε i α)
  (f : α → Parser σ τ ε j β)
  (g : β → Parser σ τ ε k γ)
  : (x >>=ᵍ f >>=ᵍ g) ≍ (x >>=ᵍ fun a => f a >>=ᵍ g) := by
  have hc := congrArg Grade.consumes (mul_assoc i j k)
  apply Parser.heq (mul_assoc i j k)
  intro m t
  obtain ⟨xr, xs⟩ := x
  simp only [gbind, bind_run]
  cases xr t with
  | failure e => exact Outcome.failure_congr hc
  | success a =>
    dsimp only
    cases f a.result |>.run (t.dropTo a.restSize a.le) with
    | failure e => exact Outcome.failure_congr hc
    | success b =>
      simp only [Success.seq_result, Success.seq_restSize, Input.dropTo_trans]
      cases g b.result |>.run (t.dropTo b.restSize (b.le.trans a.le)) with
      | failure e => exact Outcome.failure_congr hc
      | success c => exact Outcome.success_congr hc Success.seq_assoc

theorem gmap_gpure
  (G : α → β)
  (x : α)
  : (G <$>ᵍ (gpure x : Parser σ τ ε 1 α)) = gpure (G x) := by
  ext m t; simp [GradedFunctor.gmap, gpure, Functor.map]

theorem gpure_gseq
  {i : Grade}
  (G : α → β)
  (x : Parser σ τ ε i α)
  : (gpure G <*>ᵍ fun () => x) ≍ (G <$>ᵍ x) := by
  have hc := congrArg Grade.consumes (one_mul i)
  apply Parser.heq (one_mul i)
  intro m t
  obtain ⟨xr, xs⟩ := x
  simp only [GradedApplicative.gseq, GradedFunctor.gmap, gpure, bind_run, Functor.map,
             Input.dropTo_self]
  exact match xr t with
  | failure e => Outcome.failure_congr hc
  | success y => Outcome.success_congr hc (Success.heq hc)

theorem gseq_gpure
  {i : Grade}
  (u : Parser σ τ ε i (α → β))
  (x : α)
  : (u <*>ᵍ fun () => gpure x) ≍ ((· x) <$>ᵍ u) := by
  have hc := congrArg Grade.consumes (mul_one i)
  apply Parser.heq (mul_one i)
  intro m t
  obtain ⟨ur, us⟩ := u
  simp only [GradedApplicative.gseq, GradedFunctor.gmap, bind_run, Functor.map]
  exact match ur t with
  | failure e => Outcome.failure_congr hc
  | success y => Outcome.success_congr hc (Success.heq hc)

theorem gseq_assoc
  {i j k : Grade}
  (u : Parser σ τ ε i (β → γ))
  (v : Parser σ τ ε j (α → β))
  (w : Parser σ τ ε k α)
  : ((Function.comp <$>ᵍ u <*>ᵍ fun () => v) <*>ᵍ fun () => w)
      ≍ (u <*>ᵍ fun () => (v <*>ᵍ fun () => w)) := by
  have hc := congrArg Grade.consumes (mul_assoc i j k)
  apply Parser.heq (mul_assoc i j k)
  intro m t
  obtain ⟨ur, us⟩ := u
  simp only [GradedApplicative.gseq, GradedFunctor.gmap, bind_run, Functor.map]
  cases ur t with
  | failure e => exact Outcome.failure_congr hc
  | success a =>
    dsimp only
    cases v.run (t.dropTo a.restSize a.le) with
    | failure e => exact Outcome.failure_congr hc
    | success b =>
      simp
      cases w.run (t.dropTo b.restSize (b.le.trans a.le)) with
      | failure e => exact Outcome.failure_congr hc
      | success c => exact Outcome.success_congr hc Success.seq_assoc

instance : LawfulGradedApplicative (Parser σ τ ε) where
  gmap_gpure := gmap_gpure
  gpure_gseq := gpure_gseq
  gseq_gpure := gseq_gpure
  gseq_assoc := gseq_assoc

instance : LawfulGradedMonad (Parser σ τ ε) where
  gpure_gbind := gpure_gbind
  gbind_gpure := gbind_gpure
  gbind_assoc := gbind_assoc

end Parser
