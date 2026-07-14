import PrimParser.Basic

/-!
# PrimParser Lawfulness Proofs

Lawful instances for `Success`, `Outcome`, and `Parser`:
`LawfulFunctor`, `LawfulGradedFunctor`, `LawfulGradedApplicative`, `LawfulGradedMonad`.
-/

namespace Parser

variable {α β γ ε : Type} {n m : Nat} {g : Grade} {ge gc : Necessity}

@[ext] theorem Parser.ext {p q : Parser ε g α}
    (h : ∀ {m} (t : Text m), p.run t = q.run t) : p = q := by
  obtain ⟨pr, ps⟩ := p; obtain ⟨qr, qs⟩ := q
  have hr : @pr = @qr := by funext m t; exact h t
  subst hr; rfl

instance : LawfulFunctor (Success n gc) where
  map_const := rfl
  id_map x := by cases x; rfl
  comp_map g h x := by cases x; rfl

instance : LawfulFunctor (Outcome ε n g) where
  map_const := rfl
  id_map x := by
    cases x with
    | inl e => rfl
    | inr r => exact congrArg Sum.inr (id_map r)
  comp_map f h x := by
    cases x with
    | inl e => rfl
    | inr r => exact congrArg Sum.inr (comp_map f h r)

instance : LawfulGradedFunctor (Success n) where
  gmap_id x := by cases x; rfl
  gmap_comp g h x := by cases x; rfl

instance : LawfulGradedFunctor (Parser ε) where
  gmap_id x := by ext m t; simp only [GradedFunctor.gmap]; exact id_map (x.run t)
  gmap_comp g h x := by ext m t; simp only [GradedFunctor.gmap]; exact comp_map h g (x.run t)

theorem Parser.heq {g₁ g₂ : Grade} {p : Parser ε g₁ α} {q : Parser ε g₂ α}
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

theorem Success.seq_assoc {gc gc' gc'' : Necessity} (a : Success n gc α)
    (b : Success a.restSize gc' β) (c : Success b.restSize gc'' γ)
    : HEq ((a.seq b).seq c) (a.seq (b.seq c)) :=
  Success.heq (sup_assoc _ _ _) rfl rfl HEq.rfl

@[simp] theorem Success.seq_result {gc gc' : Necessity} (a : Success n gc α)
    (b : Success a.restSize gc' β) : (a.seq b).result = b.result := rfl
@[simp] theorem Success.seq_restText {gc gc' : Necessity} (a : Success n gc α)
    (b : Success a.restSize gc' β) : (a.seq b).restText = b.restText := rfl

theorem Outcome.heq_inl {g₁ g₂ : Grade} {α : Type} (hc : g₁.consumes = g₂.consumes)
    {f₁ f₂ : Failure n ε} (hf : f₁ = f₂)
    : HEq (Sum.inl f₁ : Outcome ε n g₁ α) (Sum.inl f₂ : Outcome ε n g₂ α) := by
  obtain ⟨e₁, c₁⟩ := g₁; obtain ⟨e₂, c₂⟩ := g₂; dsimp only at hc; subst hc; subst hf; rfl

theorem Outcome.heq_inr {g₁ g₂ : Grade} (hc : g₁.consumes = g₂.consumes)
    {s₁ : Success n g₁.consumes α} {s₂ : Success n g₂.consumes α} (hs : HEq s₁ s₂)
    : HEq (Sum.inr s₁ : Outcome ε n g₁ α) (Sum.inr s₂ : Outcome ε n g₂ α) := by
  obtain ⟨e₁, c₁⟩ := g₁; obtain ⟨e₂, c₂⟩ := g₂; dsimp only at hc hs; subst hc
  cases eq_of_heq hs; rfl

theorem parser_gpure_gbind {j : Grade} (a : α) (f : α → Parser ε j β)
    : (gpure a >>=ᵍ f) ≍ f a := by
  apply Parser.heq (one_mul j)
  intro m t
  simp only [gbind, gpure, bind, Outcome.ofSuccess]
  cases (f a).run t with
  | inl e => simp
  | inr y => cases y; simp [Success.seq, Success.le, Necessity.never_sup]

theorem parser_gbind_gpure {i : Grade} (p : Parser ε i α)
    : (p >>=ᵍ gpure) ≍ p := by
  apply Parser.heq (mul_one i)
  intro m t
  obtain ⟨pr, ps⟩ := p
  simp only [gbind, gpure, bind, Outcome.ofSuccess]
  cases pr t with
  | inl e => dsimp only; exact Outcome.heq_inl (congrArg Grade.consumes (mul_one i)) rfl
  | inr x =>
    dsimp only
    exact Outcome.heq_inr (congrArg Grade.consumes (mul_one i))
      (Success.heq (congrArg Grade.consumes (mul_one i)) rfl rfl HEq.rfl)

theorem parser_gbind_assoc {i j k : Grade}
    (x : Parser ε i α) (f : α → Parser ε j β) (g : β → Parser ε k γ)
    : (x >>=ᵍ f >>=ᵍ g) ≍ (x >>=ᵍ fun a => f a >>=ᵍ g) := by
  apply Parser.heq (mul_assoc i j k)
  intro m t
  obtain ⟨xr, xs⟩ := x
  simp only [gbind, bind]
  cases xr t with
  | inl e => dsimp only; exact Outcome.heq_inl (congrArg Grade.consumes (mul_assoc i j k)) rfl
  | inr a =>
    dsimp only
    cases (f a.result).run a.restText with
    | inl e => dsimp only; exact Outcome.heq_inl (congrArg Grade.consumes (mul_assoc i j k)) rfl
    | inr b =>
      dsimp only; simp only [Success.seq_result, Success.seq_restText]
      cases (g b.result).run b.restText with
      | inl e =>
        exact Outcome.heq_inl (congrArg Grade.consumes (mul_assoc i j k)) (by cases e; rfl)
      | inr c =>
        exact Outcome.heq_inr (congrArg Grade.consumes (mul_assoc i j k)) (Success.seq_assoc a b c)

theorem parser_gmap_gpure (G : α → β) (x : α)
    : (G <$>ᵍ (gpure x : Parser ε 1 α)) = gpure (G x) := by
  ext m t; simp [GradedFunctor.gmap, gpure, Outcome.ofSuccess, Functor.map]

theorem parser_gpure_gseq {i : Grade} (G : α → β) (x : Parser ε i α)
    : (gpure G <*>ᵍ fun () => x) ≍ (G <$>ᵍ x) := by
  apply Parser.heq (one_mul i)
  intro m t
  obtain ⟨xr, xs⟩ := x
  simp only [GradedApplicative.gseq, GradedFunctor.gmap, gpure, bind, Outcome.ofSuccess, Functor.map]
  cases xr t with
  | inl e => dsimp only; exact Outcome.heq_inl (congrArg Grade.consumes (one_mul i)) rfl
  | inr y =>
    dsimp only
    exact Outcome.heq_inr (congrArg Grade.consumes (one_mul i))
      (Success.heq (congrArg Grade.consumes (one_mul i)) rfl rfl HEq.rfl)

theorem parser_gseq_gpure {i : Grade} (u : Parser ε i (α → β)) (x : α)
    : (u <*>ᵍ fun () => gpure x) ≍ ((· x) <$>ᵍ u) := by
  apply Parser.heq (mul_one i)
  intro m t
  obtain ⟨ur, us⟩ := u
  simp only [GradedApplicative.gseq, GradedFunctor.gmap, gpure, bind, Outcome.ofSuccess, Functor.map]
  cases ur t with
  | inl e => dsimp only; exact Outcome.heq_inl (congrArg Grade.consumes (mul_one i)) rfl
  | inr y =>
    dsimp only
    exact Outcome.heq_inr (congrArg Grade.consumes (mul_one i))
      (Success.heq (congrArg Grade.consumes (mul_one i)) rfl rfl HEq.rfl)

theorem parser_gseq_assoc {i j k : Grade}
    (u : Parser ε i (β → γ)) (v : Parser ε j (α → β)) (w : Parser ε k α)
    : ((Function.comp <$>ᵍ u <*>ᵍ fun () => v) <*>ᵍ fun () => w)
      ≍ (u <*>ᵍ fun () => (v <*>ᵍ fun () => w)) := by
  apply Parser.heq (mul_assoc i j k)
  intro m t
  obtain ⟨ur, us⟩ := u
  simp only [GradedApplicative.gseq, GradedFunctor.gmap, bind, Functor.map]
  cases ur t with
  | inl e => dsimp only; exact Outcome.heq_inl (congrArg Grade.consumes (mul_assoc i j k)) rfl
  | inr a =>
    dsimp only
    cases (v.run a.restText) with
    | inl e => dsimp only; exact Outcome.heq_inl (congrArg Grade.consumes (mul_assoc i j k)) rfl
    | inr b =>
      dsimp only; simp only [Success.seq_result, Success.seq_restText]
      cases (w.run b.restText) with
      | inl e => exact Outcome.heq_inl (congrArg Grade.consumes (mul_assoc i j k)) (by cases e; rfl)
      | inr c =>
        exact Outcome.heq_inr (congrArg Grade.consumes (mul_assoc i j k))
          (Success.heq (sup_assoc _ _ _) rfl rfl HEq.rfl)

instance : LawfulGradedApplicative (Parser ε) where
  gmap_gpure := parser_gmap_gpure
  gpure_gseq := parser_gpure_gseq
  gseq_gpure := parser_gseq_gpure
  gseq_assoc := parser_gseq_assoc

instance : LawfulGradedMonad (Parser ε) where
  gpure_gbind := parser_gpure_gbind
  gbind_gpure := parser_gbind_gpure
  gbind_assoc := parser_gbind_assoc

end Parser

