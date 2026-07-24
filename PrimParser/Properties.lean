import PrimParser.Basic

/-!
# PrimParser Lawfulness Proofs

Lawful instances for `Success`, `Outcome`, and `Parser`:
`LawfulFunctor`, `LawfulGradedFunctor`, `LawfulGradedApplicative`, `LawfulGradedMonad`.
-/

namespace Parser

variable
  {α β γ ε : Type}
  {n m : Nat}
  {g : Grade}
  {ge gc : Necessity}

@[ext] theorem ext {p q : Parser ε g α}
    (h : ∀ {m} (t : Text m), p.run t = q.run t) : p = q := by
  obtain ⟨pr, ps⟩ := p; obtain ⟨qr, qs⟩ := q
  have hr : @pr = @qr := by funext m t; exact h t
  subst hr; rfl

instance : LawfulFunctor (Success n gc) where
  map_const := rfl
  id_map x := by cases x; rfl
  comp_map g h x := by cases x; rfl

instance : LawfulFunctor (Outcome ε n gc) where
  map_const := rfl
  id_map x := by cases x <;> simp [Functor.map]
  comp_map f h x := by cases x <;> simp [Functor.map]

instance : LawfulGradedFunctor (Success n) where
  gmap_id x := by cases x; rfl
  gmap_comp g h x := by cases x; rfl

instance : LawfulGradedFunctor (Parser ε) where
  -- TODO review 44 begin
  gmap_id x := by ext m t; simp only [GradedFunctor.gmap]; exact id_map (x.run t)
  gmap_comp g h x := by ext m t; simp only [GradedFunctor.gmap]; exact comp_map h g (x.run t)

theorem heq {g₁ g₂ : Grade} {p : Parser ε g₁ α} {q : Parser ε g₂ α}
    (hg : g₁ = g₂) (h : ∀ {m} (t : Text m), HEq (p.run t) (q.run t)) : HEq p q := by
  subst hg; apply heq_of_eq; ext m t; exact eq_of_heq (h t)

@[simp] theorem Failure.trans_self (e : Failure n ε) (h : n ≤ n) : e.trans h = e := by
  cases e; rfl

@[simp] theorem Necessity.never_sup (a : Necessity) : never ⊔ a = a := by cases a <;> rfl
@[simp] theorem Necessity.sup_never (a : Necessity) : a ⊔ never = a := by cases a <;> rfl

theorem Success.heq {c₁ c₂ : Necessity} (hc : c₁ = c₂)
    {s₁ : Success n c₁ α} {s₂ : Success n c₂ α}
    (hr : s₁.result = s₂.result) (hrs : s₁.restSize = s₂.restSize)
    (hrt : HEq s₁.restText s₂.restText) : HEq s₁ s₂ := by
  subst hc; apply heq_of_eq; cases s₁; cases s₂; simp_all

theorem Success.seq_assoc {gc' gc'' : Necessity} (a : Success n gc α)
    (b : Success a.restSize gc' β) (c : Success b.restSize gc'' γ)
    : HEq ((a.seq b).seq c) (a.seq (b.seq c)) :=
  Success.heq (sup_assoc _ _ _) rfl rfl HEq.rfl

@[simp] theorem Success.seq_result {gc' : Necessity} (a : Success n gc α)
    (b : Success a.restSize gc' β) : (a.seq b).result = b.result := rfl
@[simp] theorem Success.seq_restText {gc' : Necessity} (a : Success n gc α)
    (b : Success a.restSize gc' β) : (a.seq b).restText = b.restText := rfl

theorem Outcome.heq_failure {c₁ c₂ : Necessity} (hc : c₁ = c₂)
    {f₁ f₂ : Failure n ε} (hf : f₁ = f₂)
    : HEq (failure f₁ : Outcome ε n c₁ α) (failure f₂ : Outcome ε n c₂ α) := by
  subst hf; exact hc ▸ HEq.rfl

theorem Outcome.heq_success {c₁ c₂ : Necessity} (hc : c₁ = c₂)
    {s₁ : Success n c₁ α} {s₂ : Success n c₂ α} (hs : HEq s₁ s₂)
    : HEq (success s₁ : Outcome ε n c₁ α) (success s₂ : Outcome ε n c₂ α) := by
  subst hc; cases eq_of_heq hs; rfl

theorem bind_run {g g' : Grade} (m : Parser ε g α) (f : α → Parser ε g' β) (t : Text n)
    : (bind m f).run t
      = match m.run t with
        | failure e => failure e
        | success x => match f x.result |>.run x.restText with
          | failure e => failure (e.trans x.le)
          | success y => success (x.seq y) := by
  cases hm : m.run t with
  | failure e =>
    simp only [bind, Parser.handle]; simp only [hm]
    simp only [Outcome.handle, Outcome.throwFailure]
  | success x =>
    simp only [bind, Parser.handle]; simp only [hm]
    simp only [Outcome.handle, Success.bindParser]
    cases (f x.result).run x.restText <;> rfl

theorem parser_gpure_gbind {j : Grade} (a : α) (f : α → Parser ε j β)
    : (gpure a >>=ᵍ f) ≍ f a := by
  apply Parser.heq (one_mul j)
  intro m t
  simp only [gbind, gpure, bind_run, Outcome.ofSuccess]
  cases (f a).run t with
  | failure e => simp
  | success y => cases y; simp [Success.seq]

theorem parser_gbind_gpure {i : Grade} (p : Parser ε i α)
    : (p >>=ᵍ gpure) ≍ p := by
  have hc := congrArg Grade.consumes (mul_one i)
  apply Parser.heq (mul_one i)
  intro m t
  obtain ⟨pr, ps⟩ := p
  simp only [gbind, gpure, bind_run, Outcome.ofSuccess]
  exact match pr t with
  | failure e => Outcome.heq_failure hc rfl
  | success x => Outcome.heq_success hc (Success.heq hc rfl rfl HEq.rfl)

theorem parser_gbind_assoc {i j k : Grade}
    (x : Parser ε i α) (f : α → Parser ε j β) (g : β → Parser ε k γ)
    : (x >>=ᵍ f >>=ᵍ g) ≍ (x >>=ᵍ fun a => f a >>=ᵍ g) := by
  have hc := congrArg Grade.consumes (mul_assoc i j k)
  apply Parser.heq (mul_assoc i j k)
  intro m t
  obtain ⟨xr, xs⟩ := x
  simp only [gbind, bind_run]
  cases xr t with
  | failure e => exact Outcome.heq_failure hc rfl
  | success a =>
    dsimp only
    cases (f a.result).run a.restText with
    | failure e => exact Outcome.heq_failure hc rfl
    | success b =>
      simp only [Success.seq_result, Success.seq_restText]
      cases (g b.result).run b.restText with
      | failure e => exact Outcome.heq_failure hc (by cases e; rfl)
      | success c => exact Outcome.heq_success hc (Success.seq_assoc a b c)

theorem parser_gmap_gpure (G : α → β) (x : α)
    : (G <$>ᵍ (gpure x : Parser ε 1 α)) = gpure (G x) := by
  ext m t; simp [GradedFunctor.gmap, gpure, Outcome.ofSuccess, Functor.map]

theorem parser_gpure_gseq {i : Grade} (G : α → β) (x : Parser ε i α)
    : (gpure G <*>ᵍ fun () => x) ≍ (G <$>ᵍ x) := by
  have hc := congrArg Grade.consumes (one_mul i)
  apply Parser.heq (one_mul i)
  intro m t
  obtain ⟨xr, xs⟩ := x
  simp only [GradedApplicative.gseq, GradedFunctor.gmap, gpure, bind_run, Outcome.ofSuccess, Functor.map]
  cases xr t with
  | failure e => exact Outcome.heq_failure hc rfl
  | success y => exact Outcome.heq_success hc (Success.heq hc rfl rfl HEq.rfl)

theorem parser_gseq_gpure {i : Grade} (u : Parser ε i (α → β)) (x : α)
    : (u <*>ᵍ fun () => gpure x) ≍ ((· x) <$>ᵍ u) := by
  have hc := congrArg Grade.consumes (mul_one i)
  apply Parser.heq (mul_one i)
  intro m t
  obtain ⟨ur, us⟩ := u
  simp only [GradedApplicative.gseq, GradedFunctor.gmap, gpure, bind_run, Outcome.ofSuccess, Functor.map]
  cases ur t with
  | failure e => exact Outcome.heq_failure hc rfl
  | success y => exact Outcome.heq_success hc (Success.heq hc rfl rfl HEq.rfl)

theorem parser_gseq_assoc {i j k : Grade}
    (u : Parser ε i (β → γ)) (v : Parser ε j (α → β)) (w : Parser ε k α)
    : ((Function.comp <$>ᵍ u <*>ᵍ fun () => v) <*>ᵍ fun () => w)
      ≍ (u <*>ᵍ fun () => (v <*>ᵍ fun () => w)) := by
  have hc := congrArg Grade.consumes (mul_assoc i j k)
  apply Parser.heq (mul_assoc i j k)
  intro m t
  obtain ⟨ur, us⟩ := u
  simp only [GradedApplicative.gseq, GradedFunctor.gmap, bind_run, Functor.map]
  cases ur t with
  | failure e => exact Outcome.heq_failure hc rfl
  | success a =>
    dsimp only
    cases (v.run a.restText) with
    | failure e => exact Outcome.heq_failure hc rfl
    | success b =>
      simp only [Success.seq_result, Success.seq_restText]
      cases (w.run b.restText) with
      | failure e => exact Outcome.heq_failure hc (by cases e; rfl)
      | success c => exact Outcome.heq_success hc (Success.heq (sup_assoc _ _ _) rfl rfl HEq.rfl)
  -- TODO review 44 end

-- TODO review 45 (deletion here)
instance : LawfulGradedApplicative (Parser ε) where
  -- TODO review 46 begin
  gmap_gpure := parser_gmap_gpure
  gpure_gseq := parser_gpure_gseq
  gseq_gpure := parser_gseq_gpure
  gseq_assoc := parser_gseq_assoc
  -- TODO review 46 end

instance : LawfulGradedMonad (Parser ε) where
  -- TODO review 47 begin
  gpure_gbind := parser_gpure_gbind
  gbind_gpure := parser_gbind_gpure
  gbind_assoc := parser_gbind_assoc
  -- TODO review 47 end

end Parser
