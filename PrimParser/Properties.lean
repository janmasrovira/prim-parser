import PrimParser.Basic

/-!
# PrimParser Lawfulness Proofs

Lawful instances for `Success`, `Outcome`, and `Parser`:
`LawfulFunctor`, `LawfulGFunctor`, `LawfulGApplicative`, `LawfulGMonad`.
-/

namespace Parser

variable
  {α β γ ε : Type}
  {n : Nat}
  {g : Grade}
  {ge gc : Necessity}

instance : LawfulFunctor (Success n gc) where
  map_const := rfl
  id_map x := by cases x; rfl
  comp_map g h x := by cases x; rfl

instance : LawfulFunctor (Outcome ε n g) where
  map_const := by simp [Functor.mapConst, Functor.map]
  id_map x := by
    rcases g with ⟨ge, gc⟩; cases ge <;> simp [Outcome] at x
    · apply id_map x
    · simp [Functor.map]
    · apply id_map x
  comp_map {α} β γ f h x := by
    rcases g with ⟨ge, gc⟩; cases ge <;> simp [Outcome] at x
    · cases x <;> simp [Functor.map, Sum.bind]
    · simp [Functor.map]
    · apply comp_map f h x

instance : LawfulGFunctor (Success n) where
  gmap_id x := by cases x; rfl
  gmap_comp g h x := by cases x; rfl

instance : LawfulGFunctor (Parser ε) where
  gmap_comp := by intro g _ _ _ f h p; simp [GFunctor.gmap]; ext n t; congr
  gmap_id := by intro g α ⟨p⟩; simp [GFunctor.gmap]

theorem gbind_assoc
  {ge1 gc1 ge2 gc2 ge3 gc3 : Necessity}
  (p1 : Parser ε ⟨ge1, gc1⟩ α)
  (p2 : α → Parser ε ⟨ge2, gc2⟩ β)
  (p3 : β → Parser ε ⟨ge3, gc3⟩ γ)
  : (p1 >>=ᵍ p2 >>=ᵍ p3) ≍ (p1 >>=ᵍ fun a => p2 a >>=ᵍ p3) := by
  obtain ⟨p⟩ := p1
  cases ge1
  · case possibly =>
    simp [gbind, bind]
    congr 1
    · grind
    · simp [HMul.hMul, Mul.mul]
      refine Function.hfunext rfl ?_; intro _ _ .rfl
      refine Function.hfunext rfl ?_; intro t _ .rfl
      cases ge2 <;> simp
      · cases p t <;> simp [Outcome.throw, Success.bindParser]
        · cases ge3 <;> simp <;> congr 2 <;> apply max_assoc
        · next v =>
          cases ge3 <;> simp
          · cases p2 v.result |>.run v.restText <;> simp [Success.seq]
            · congr 2; apply max_assoc
            · next v =>
              cases p3 v.result |>.run v.restText <;> simp
              · congr 2; apply max_assoc
              · congr 2
                · apply max_assoc
                · apply max_assoc
                · apply proof_irrel_heq
          · cases p2 v.result |>.run v.restText <;> simp [Success.seq]
          · cases p2 v.result |>.run v.restText <;> simp [Success.seq]
            · congr 2; apply max_assoc
            · congr 2
              · apply max_assoc
              · apply max_assoc
              · apply proof_irrel_heq
      · cases p t <;> simp [Outcome.throw, Success.bindParser]
      · cases p t <;> simp [Outcome.throw, Success.bindParser]
        · cases ge3 <;> simp <;> congr 2 <;> apply max_assoc
        · next v =>
          cases ge3 <;> simp [Success.seq]
          · case possibly =>
            cases p3 (p2 v.result |>.run v.restText).result |>.run
              (p2 v.result |>.run v.restText).restText <;> simp
            · congr 2; apply max_assoc
            · congr 2
              · apply max_assoc
              · apply max_assoc
              · apply proof_irrel_heq
          · case never =>
            congr 2
            · apply max_assoc
            · apply max_assoc
            · apply proof_irrel_heq
  · case always => simp [gbind, bind]; congr 1; grind
  · case never =>
    simp [gbind, bind]
    congr 1
    · grind
    · simp [HMul.hMul, Mul.mul, max]
      cases ge2 <;> simp
      · case possibly =>
        refine Function.hfunext rfl ?_; intro _ _ .rfl
        refine Function.hfunext rfl ?_; intro t _ .rfl
        simp [Success.bindParser, Success.seq]
        cases ge3 <;> simp
        · case possibly =>
          cases p2 (p t).result |>.run (p t).restText <;> simp [Outcome.throw]
          · congr 2; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
          · next v =>
            cases p3 v.result |>.run v.restText <;> simp
              <;> congr 2 <;> cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
        · case always =>
          cases p2 (p t).result |>.run (p t).restText <;> simp
          · rfl
        · case never =>
          cases p2 (p t).result |>.run (p t).restText <;> simp [Outcome.throw]
          · congr 2; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
          · congr 2 <;> · cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
      · case always => ext n a; simp [Success.bindParser]
      · case never =>
        cases ge3
        · case possibly =>
          refine Function.hfunext rfl ?_; intro _ _ .rfl
          refine Function.hfunext rfl ?_; intro t _ .rfl
          simp [Success.bindParser, Success.seq]
          cases p3 (p2 (p t).result |>.run (p t).restText).result |>.run
            (p2 (p t).result |>.run (p t).restText).restText <;> simp
          · congr 1; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
          · congr 1 <;> cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
        · case always =>
          simp [Success.bindParser, Success.seq]
        · case never =>
          simp [Success.bindParser, Success.seq]
          refine Function.hfunext rfl ?_; intro _ _ .rfl
          refine Function.hfunext rfl ?_; intro _ _ .rfl
          congr 1
          · cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
          · apply proof_irrel_heq

instance : LawfulGApplicative (Parser ε) where
  gmap_gpure := by intro _ _ _ _; congr
  gpure_gseq := by
    intro ⟨ge, gc⟩ α β f ⟨p⟩
    simp [GFunctor.gmap, GApplicative.gseq, bind, gpure]
    ext n t
    simp [Success.bindParser]
    cases ge <;> simp
    · cases p t <;> simp [Functor.map, Sum.bind, Success.seq]
    · cases p t; simp [Functor.map, Success.seq]

  gseq_gpure := by
    intro ⟨ge, gc⟩ α β ⟨p⟩ a
    cases ge <;> cases gc <;> simp [GFunctor.gmap, GApplicative.gseq, bind, gpure] <;> funext n t
      <;> simp [Functor.map, Success.bindParser, Success.seq, Outcome.throw, Sum.bind]
      <;> cases p t <;> simp

  gseq_assoc := by
    intro ⟨ge1, gc1⟩ ⟨ge2, gc2⟩ ⟨ge3, gc3⟩ α β γ ⟨p1⟩ ⟨p2⟩ ⟨p3⟩
    cases ge1
    · case possibly =>
      simp [GApplicative.gseq, bind]
      congr 1
      · grind
      · simp [HMul.hMul, Mul.mul]
        refine Function.hfunext rfl ?_; intro _ _ .rfl
        refine Function.hfunext rfl ?_; intro t1 t2 .rfl
        cases ge2 <;> simp [GFunctor.gmap, Functor.map, Sum.bind]
        · cases p1 t1 <;> simp [Outcome.throw, Success.bindParser]
          · cases ge3 <;> simp <;> congr 2 <;> apply max_assoc
          · next v =>
            cases ge3 <;> simp
            · case possibly =>
              cases p2 (Success.restText v) <;> simp [Success.seq]
              · congr 2; apply max_assoc
              · next v =>
                cases p3 (Success.restText v) <;> simp
                · congr 2; apply max_assoc
                · congr 2
                  · apply max_assoc
                  · apply max_assoc
                  · apply proof_irrel_heq
            · case always => cases p2 (Success.restText v) <;> simp [Success.seq]
            · case never =>
              cases p2 (Success.restText v) <;> simp [Success.seq]
              · congr 2; apply max_assoc
              · congr 2
                · apply max_assoc
                · apply max_assoc
                · apply proof_irrel_heq
        · cases p1 t1 <;> simp [Outcome.throw, Success.bindParser]
        · cases p1 t1 <;> simp [Outcome.throw, Success.bindParser]
          · cases ge3 <;> simp <;> congr 2 <;> apply max_assoc
          · next v =>
            cases ge3 <;> simp [Success.seq]
            · case possibly =>
              cases p3 (Success.restText (p2 (Success.restText v))) <;> simp
              · congr 2; apply max_assoc
              · congr 2
                · apply max_assoc
                · apply max_assoc
                · apply proof_irrel_heq
            · case never =>
              congr 2
              · apply max_assoc
              · apply max_assoc
              · apply proof_irrel_heq
    · case always => simp [GApplicative.gseq, bind]; congr 1; grind
    · case never =>
      simp [GApplicative.gseq, bind]
      congr 1
      · grind
      · simp [HMul.hMul, Mul.mul]
        cases ge2 <;> simp
        · case possibly =>
          refine Function.hfunext rfl ?_; intro _ _ .rfl
          refine Function.hfunext rfl ?_; intro t1 t2 .rfl
          simp [GFunctor.gmap, Functor.map, Success.bindParser, Sum.bind, Success.seq]
          cases ge3 <;> simp
          · case possibly =>
            cases p2 (Success.restText (p1 t1)) <;> simp [Outcome.throw]
            · congr 2; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
            · next v =>
              cases p3 (Success.restText v) <;> simp
                <;> congr 2 <;> cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
          · case always =>
            cases p2 (Success.restText (p1 t1)) <;> simp
            · rfl
          · case never =>
            cases p2 (Success.restText (p1 t1)) <;> simp [Outcome.throw]
            · congr 2; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
            · congr 2 <;> · cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
        · case always => ext n a; simp [GFunctor.gmap, Functor.map, Success.bindParser]
        · case never =>
          cases ge3
          · case possibly =>
            refine Function.hfunext rfl ?_; intro _ _ .rfl
            refine Function.hfunext rfl ?_; intro t1 t2 .rfl
            simp [GFunctor.gmap, Functor.map, Success.bindParser, Sum.bind, Success.seq]
            cases p3 (Success.restText (p2 (Success.restText (p1 t1)))) <;> simp
            · congr 1; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
            · congr 1 <;> cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
          · case always =>
            simp [GFunctor.gmap, Functor.map, Success.bindParser]
            ext n t; congr
          · case never =>
            simp [Success.bindParser, Success.seq, Functor.map, GFunctor.gmap]
            refine Function.hfunext rfl ?_; intro _ _ .rfl
            refine Function.hfunext rfl ?_; intro _ _ .rfl
            congr 1
            · cases gc1 <;> cases gc2 <;> cases gc3 <;> simp
            · apply proof_irrel_heq

instance : LawfulGMonad (Parser ε) where
  gpure_gbind := by
    intro ⟨ge, gc⟩ _ _ a f
    cases ge <;> simp [gpure, gbind, bind, Success.bindParser, Success.seq] <;> try (rcases f a with ⟨run'⟩; simp)
    · ext n t; cases run' t; simp; congr 2
    · congr

  gbind_gpure := by
    intro ⟨ge, gc⟩ _ ⟨p⟩
    simp [gpure, gbind, bind]
    congr 1
    · simp [OfNat.ofNat, One.one, HMul.hMul, Mul.mul]
    · refine Function.hfunext rfl ?_; intro _ _ .rfl
      refine Function.hfunext rfl ?_; intro t _ .rfl
      cases ge <;> simp [Outcome.throw, Success.bindParser, Success.seq]
      · case possibly =>
        cases p t <;> simp
        · congr 2; simp [OfNat.ofNat, One.one]
        · congr 2
          · simp [OfNat.ofNat, One.one, HMul.hMul, Mul.mul]
          · simp [OfNat.ofNat, One.one]
          · apply proof_irrel_heq
      · case never =>
        cases p t; simp
        congr
        · simp [OfNat.ofNat, One.one]
        · apply proof_irrel_heq

  gbind_assoc := Parser.gbind_assoc

end Parser
