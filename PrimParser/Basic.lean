import PrimParser.Base
import PrimParser.Necessity
import PrimParser.GradedMonad

abbrev Error := String
abbrev Text (n : Nat) := List.Vector Char n

structure Grade where
  errors : Necessity
  consumes : Necessity
  deriving Repr

namespace Grade

-- No parser can always consume and never fail, because it must accept empty
-- input
abbrev impossible : Grade where
  consumes := .always
  errors := .never

abbrev conditional : Grade where
  consumes := .always
  errors := .possibly

abbrev flexible : Grade where
  consumes := .possibly
  errors := .never

abbrev fallible : Grade where
  consumes := .possibly
  errors := .possibly

abbrev pure : Grade where
  consumes := .never
  errors := .never

abbrev lookahead : Grade where
  consumes := .never
  errors := .possibly

abbrev empty : Grade where
  consumes := .never
  errors := .always

@[simp] def max (a b : Grade) : Grade := ⟨a.errors ⊔ b.errors, a.consumes ⊔ b.consumes⟩

instance : Max Grade where
  max := max

instance : Monoid Grade where
  mul := max
  mul_assoc a b c := by cases a; cases b; simp [HMul.hMul, Mul.mul]; grind
  one := pure
  one_mul a := by cases a; simp [HMul.hMul, Mul.mul, OfNat.ofNat, pure]
  mul_one a := by cases a; simp [HMul.hMul, Mul.mul, OfNat.ofNat, pure]

instance : Zero Grade where
  zero := empty

variable (e1 e2 c1 c2 : Necessity)

@[simp] theorem mul_mk : (⟨e1, c1⟩ : Grade) * ⟨e2, c2⟩ = ⟨e1 ⊔ e2, c1 ⊔ c2⟩ := by
  simp [HMul.hMul, Mul.mul]

@[simp] theorem one_mk : (1 : Grade) = ⟨.never, .never⟩ := by
  simp [OfNat.ofNat, One.one]

def choice (a b : Grade) : Grade where
  errors := a.errors ⊓ b.errors
  consumes := a.errors.ite b.consumes a.consumes

end Grade

namespace Parser

variable
  {n m : Nat}
  {a gc gc' : Necessity}

abbrev consumptionWitness (n m : Nat) : Necessity → Prop
  | .always => n < m
  | .possibly => n ≤ m
  | .never => n = m

@[simp] theorem consumptionWitness.rfl : a ≤ .possibly → consumptionWitness n n a := by
  intro _; cases a <;> try simp
  contradiction

theorem consumptionWitness.le : consumptionWitness n m a → n ≤ m := by
  cases a <;> simp_all; omega

theorem consumptionWitness.min_possibly : consumptionWitness n m a → consumptionWitness n m (.possibly ⊓ a) := by
  cases a <;> grind only [Nat.le_of_succ_le]

theorem consumptionWitness.trans {n1 n2 n3 : Nat}
  (w1 : consumptionWitness n2 n1 gc)
  (w2 : consumptionWitness n3 n2 gc')
  : consumptionWitness n3 n1 (gc ⊔ gc') := by cases gc <;> cases gc' <;> omega

structure Success (n : Nat) (consumes : Necessity) (α : Type) where
  result : α
  {restSize : Nat}
  restText : Text restSize
  witness : consumptionWitness restSize n consumes := by simp

abbrev Outcome (ε : Type) (n : Nat) (g : Grade) (α : Type) : Type :=
  match g.errors with
  | .never => Success n g.consumes α
  | .possibly => ε ⊕ Success n g.consumes α
  | .always => ε

end Parser

structure Parser (ε : Type) (g : Grade) (α : Type) where
  run : ∀ {n}, Text n → Parser.Outcome ε n g α

namespace Parser

variable
  {α β γ ε ε' : Type}
  {n m : Nat}
  {g g' : Grade}
  {ge ge' : Necessity} -- used for `errors`
  {gc gc': Necessity} -- used for `consumes`

def Outcome.handle
  (p : Outcome ε n ⟨ge, gc⟩ α)
  (e : .possibly ≤ ge → ε → β)
  (s : ge ≤ .possibly → Success n gc α → β)
  : β :=
  match ge with
  | .always => e (by decide) p
  | .never => s (by decide) p
  | .possibly => match p with
    | .inl x => e (by decide) x
    | .inr x => s (by decide) x

instance : Functor (Success n gc) where
  map f x := {x with result := f x.result}

instance : GFunctor (Success n) where
  gmap := Functor.map

instance : Functor (Outcome ε n g) where
  map f x := match g with
    | ⟨e, _⟩ => match e with
     | .never => by dsimp! at x ⊢; exact f <$> x
     | .possibly => by dsimp! at x ⊢; exact (Functor.map f) <$> x
     | .always => x

def Error.eof : Error := "eof"
def Error.fail : Error := "fail"

def Success.ap
  (r1 : Success n gc (α → β))
  (r2 : Success r1.restSize gc' α)
  : Success n (gc ⊔ gc') β where
  result := r1.result r2.result
  restSize := r2.restSize
  restText := r2.restText
  witness := by
    have w1 := r1.witness
    have w2 := r2.witness
    cases gc <;> cases gc' <;> omega

def Success.ap'
  (r1 : Success n gc α)
  (r2 : Success r1.restSize gc' (α → β))
  : Success n (gc ⊔ gc') β where
  result := r2.result r1.result
  restSize := r2.restSize
  restText := r2.restText
  witness := by
    have w1 := r1.witness
    have w2 := r2.witness
    cases gc <;> cases gc' <;> omega

def Success.seq
  (r1 : Success n gc α)
  (r2 : Success r1.restSize gc' β)
  : Success n (gc ⊔ gc') β where
  result := r2.result
  restSize := r2.restSize
  restText := r2.restText
  witness := by
    have w1 := r1.witness
    have w2 := r2.witness
    cases gc <;> cases gc' <;> omega

def Success.bindParser {xc fe fc : Necessity}
  (x : Success n xc α)
  (f : α → Parser ε ⟨fe, fc⟩ β)
  : Outcome ε n ⟨fe, xc ⊔ fc⟩ β :=
  match fe with
  | .always => (f x.result).run x.restText
  | .never => x.seq ((f x.result).run x.restText)
  | .possibly => match (f x.result).run x.restText with
    | .inr y => .inr (x.seq y)
    | .inl e => .inl e

instance : GFunctor (Parser ε) where
  gmap f p := ⟨fun t => f <$> p.run t⟩

def Outcome.throw (e : ε) (h : .possibly ≤ g.errors := by simp) : Outcome ε n g α := by
  rcases g with ⟨g1, g2⟩
  match h : g1 with
  | .possibly => exact .inl e
  | .always => exact e
  | .never => contradiction

def Outcome.ofSuccess (r : Success n gc α) (c : ge ≤ .possibly := by decide) : Outcome ε n ⟨ge, gc⟩ α :=
  match ge with
  | .never => r
  | .possibly => .inr r
  | .always => nomatch c

def bind
  (m : Parser ε g α)
  (f : α → Parser ε g' β)
  : Parser ε (g * g') β :=
  ⟨fun t => by
  rcases g with ⟨ge, gc⟩; rcases g' with ⟨ge', gc'⟩
  have x := m.run t
  exact match ge with
  | .always => x
  | .never => x.bindParser f
  | .possibly => match x with
    | .inl e => Outcome.throw (g := ⟨max .possibly _, _⟩) e
    | .inr x' => match ge' with
      | .always => x'.bindParser f
      | .never => .inr (x'.bindParser f)
      | .possibly => x'.bindParser f⟩

instance : IsEmpty (Parser ε .impossible α) where
  false p := by cases p.run ⟨[], rfl⟩; contradiction

abbrev pure (a : α) : Parser ε 1 α where
  run t := ⟨a, t, rfl⟩

instance : GApplicative (Parser ε) where
  gpure := pure
  gseq f g := bind f fun f' => ⟨fun t => f' <$> (g ()).run t⟩

instance : GMonad (Parser ε) where
  gbind := bind

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

private theorem consumptionWitness.ite_right
  (c : .possibly ≤ ge')
  (w : consumptionWitness n m gc)
  : consumptionWitness n m (ge'.ite gc gc') := by
  cases ge' <;> cases gc <;> cases gc' <;> first | contradiction | simp; omega

private theorem consumptionWitness.ite_left
  (c : ge' ≤ .possibly)
  (w : consumptionWitness n m gc')
  : consumptionWitness n m (ge'.ite gc gc') := by
  cases ge' <;> cases gc <;> cases gc' <;> first | contradiction | simp; omega

def choice
  (p1 : Parser ε ⟨ge, gc⟩ α)
  (p2 : Parser ε ⟨ge', gc'⟩ α)
  : Parser ε ⟨ge ⊓ ge', ge.ite gc' gc⟩ α where
  run t := match ge with
    | .never => cast (by simp) (p1.run t)
    | .always => by simpa using p2.run t
    | .possibly => match p1.run t with
      | .inl _ => match ge' with
        | .never =>
          let r := p2.run t
          { r with witness := consumptionWitness.ite_right le_rfl r.witness }
        | .always => .inl (p2.run t)
        | .possibly => match p2.run t with
          | .inl e => .inl e
          | .inr r => .inr { r with witness := consumptionWitness.ite_right le_rfl r.witness }
      | .inr r =>
        let r' := { r with witness := consumptionWitness.ite_left le_rfl r.witness }
        match ge' with
        | .never => r'
        | .possibly | .always => .inr r'

def oneOf (l : List (Parser ε g α)) (p : l.length ≠ 0 := by simp) : Parser ε g α := match l with
  | [] => nomatch p
  | [x] => x
  | x :: y :: xs => by refine cast ?_ (choice x (oneOf (y :: xs)))
                       congr 2 <;> simp

def throw (e : ε) (c : .possibly ≤ ge := by simp) : Parser ε ⟨ge, gc⟩ α where
  run _ := Outcome.throw (h := c) e

-- relax: cap at .possibly via ⊓ .possibly (preserves .never, softens .always → .possibly)

def Success.relaxConsumes (p : Success n gc α) : Success n (gc ⊓ .possibly) α :=
  match gc with
  | .never => p
  | .possibly => p
  | .always => { p with witness := le_of_lt p.witness }

def relaxConsumes (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge, gc ⊓ .possibly⟩ α where
  run t :=
    (p.run t).handle
      (fun h e => Outcome.throw (h := h) e)
      (fun h r => Outcome.ofSuccess (c := h) r.relaxConsumes)

def relaxErrors (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge ⊓ .possibly, gc⟩ α where
  run t :=
    (p.run t).handle
      (fun h e => Outcome.throw (h := le_inf h le_rfl) e)
      (fun _ r => Outcome.ofSuccess (c := inf_le_right) r)

def relax (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge ⊓ .possibly, gc ⊓ .possibly⟩ α :=
  p.relaxErrors.relaxConsumes

def Success.weakenConsumes (p : Success n gc α) : Success n .possibly α :=
  match gc with
  | .never => { p with witness := le_of_eq p.witness }
  | .possibly => p
  | .always => { p with witness := le_of_lt p.witness }

def weakenConsumes (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge, .possibly⟩ α where
  run t :=
    (p.run t).handle
      (fun h e => Outcome.throw (h := h) e)
      (fun h r => Outcome.ofSuccess (c := h) r.weakenConsumes)

def weakenErrors (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨.possibly, gc⟩ α where
  run t :=
    (p.run t).handle
      (fun _ e => .inl e)
      (fun _ r => .inr r)

def weaken (p : Parser ε ⟨ge, gc⟩ α) : Parser ε .fallible α :=
  p.weakenErrors.weakenConsumes

def runOption (p : Parser ε ⟨ge, gc⟩ α) (t : Text n) : Option (Success n gc α) :=
  p.run t |>.handle (fun _ _ => .none) (fun _ r => .some r)

def runResult? (p : Parser ε ⟨ge, gc⟩ α) (t : Text n) : Option α :=
  p.run t |>.handle (fun _ _ => .none) (fun _ r => .some r.result)

def anyChar : Parser Error .conditional Char where
  run {n} t :=
    match n, t with
    | 0, .nil => .inl Error.eof
    | Nat.succ n, ⟨c :: cs, p⟩ =>
      .inr {result := c
            restSize := n
            restText := by refine ⟨cs, by simpa [List.length_cons] using p⟩
            witness := by simp}

-- Like `gpure` but with a flexible grade: both `ge` and `gc` can be `.never`
-- or `.possibly`. This lets `ok` unify with fallible or consuming parsers
-- in match branches where all arms must share the same grade.
def ok (a : α) (he : ge ≤ .possibly := by simp) (hc : gc ≤ .possibly := by simp)
  : Parser ε ⟨ge, gc⟩ α := match gc with
  | .always => nomatch hc
  | .possibly => weakenConsumes (match h : ge with
              | .possibly => weakenErrors (gpure a)
              | .never => gpure a
              | .always => by rw [h] at he; contradiction)
  | .never => match h : ge with
              | .possibly => weakenErrors (gpure a)
              | .never => gpure a

def token (f : Char → Option α) : Parser Error .conditional α := gdo
  let c ← anyChar
  match f c with
  | .some r => ok (gc := .never) r
  | .none => throw (ge := .possibly) Error.fail

def satisfy (f : Char → Bool) : Parser Error .conditional Char :=
  token (fun c => if f c then .some c else .none)

def char (c : Char) : Parser Error .conditional PUnit :=
  (fun _ => ()) <$>ᵍ satisfy (· == c)

def string (str : String) : Parser Error .conditional PUnit :=
  let rec go : List Char → Parser Error .conditional PUnit
    | [] => throw Error.fail
    | [c] => (fun _ => ()) <$>ᵍ satisfy (· == c)
    | c :: cs => gdo
      satisfy (· == c)
      go cs
  go str.toList

def optional (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨.never, ge.complement ⊓ gc⟩ (Option α) where
  run t := match ge with
    | .never => .some <$> p.run t
    | .always => {result := .none, restText := t}
    | .possibly =>
      match p.run t with
      | .inl _ => {result := .none, restText := t}
      | .inr r => {result := .some r.result
                   restText := r.restText
                   witness := r.witness.min_possibly}

def optionalBind
  (p : Parser ε ⟨ge, gc⟩ α)
  (cont : α → Parser ε ⟨ge', gc'⟩ β)
  : Parser ε ⟨.never, (ge ⊔ ge').complement ⊓ (gc ⊔ gc')⟩ (Option β) :=
  optional (gdo
    let a ← p
    cont a
    grade_by by simp)

private def manyTillGo
  (p : Parser ε ⟨ge, .always⟩ α)
  (e : Parser ε ⟨ge', gc'⟩ β)
  (h : ge ≤ .possibly)
  {n} (t : Text n)
  : Outcome ε n ⟨ge, .possibly⟩ (List α) :=
  match e.runOption t with
  | .some _ => Outcome.ofSuccess (c := h) {result := [], restText := t}
  | .none =>
    p.run t |>.handle
      (fun h err => Outcome.throw (h := h) err)
      (fun _ r =>
        have : r.restSize < n := r.witness
        (manyTillGo p e h r.restText).handle
          (fun h err => Outcome.throw (h := h) err)
          (fun _ rest =>
            Outcome.ofSuccess (c := h)
              {result := r.result :: rest.result
               restText := rest.restText
               witness := by have := rest.witness; omega}))

def manyTill
  (p : Parser ε ⟨ge, .always⟩ α)
  (e : Parser ε ⟨ge', gc'⟩ β)
  : Parser ε ⟨ge, .possibly⟩ (List α) where
  run t := match ge with
    | .always => p.run t
    | .never => manyTillGo p e (by decide) t
    | .possibly => manyTillGo p e (by decide) t

def many (p : Parser ε ⟨ge, .always⟩ α) : Parser ε .flexible (List α) where
  run :=
    let rec go {n} (p : Parser ε ⟨ge, .always⟩ α) (t : Text n)
        : Success n .possibly (List α) :=
      match p.runOption t with
      | .none => {result := [], restText := t}
      | .some r =>
        have : r.restSize < n := r.witness
        let rest := go p r.restText
        {result := r.result :: rest.result
         restText := rest.restText
         witness := by have := rest.witness; omega}
    go p

def many1 (p : Parser ε ⟨ge, .always⟩ α) : Parser ε ⟨ge, .always⟩ (List α) := gdo
  let x ← p
  let xs ← many p
  return (x :: xs)
  grade_by by simp

def takeWhile (f : Char → Bool) : Parser Error .flexible String :=
  String.ofList <$>ᵍ many (satisfy f)

def takeWhile1 (f : Char → Bool) : Parser Error .conditional String :=
  String.ofList <$>ᵍ many1 (satisfy f)

def skipWhile (f : Char → Bool) : Parser Error .flexible PUnit :=
  (fun _ => ()) <$>ᵍ takeWhile f

def skipWhile1 (f : Char → Bool) : Parser Error .conditional PUnit :=
  (fun _ => ()) <$>ᵍ takeWhile1 f

def whitespace : Parser Error .flexible PUnit :=
  skipWhile Char.isWhitespace

def whitespace1 : Parser Error .conditional PUnit :=
  skipWhile1 Char.isWhitespace

def lexeme (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge, gc ⊔ .possibly⟩ α := gdo
  let r ← p
  whitespace
  return r
  grade_by by simp

def digit : Parser Error .conditional Nat :=
  token fun c => if c.isDigit then some (c.toNat - '0'.toNat) else none

def nat : Parser Error .conditional Nat := gdo
  let d ← digit
  let ds ← many digit
  return ds.foldl (fun acc d => acc * 10 + d) d
  grade_by by simp

def int : Parser Error .conditional Int := gdo
  let neg ← optional (char '-')
  let n ← nat
  return if neg.isSome then -n else n
  grade_by by simp

def sepBy
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  (h : gc' ⊔ gc = .always := by simp)
  : Parser ε .flexible (List α) := gdo
  let m ← optional p
  match m with
  | .some f =>
    let item : Parser ε ⟨ge' ⊔ ge, .always⟩ α := gdo
        sep; p
        grade_by by simp [h]
    let rest ← many item
    ok (gc := .possibly) (f :: rest)
  | .none => ok (ge := .never) []
  grade_by by simp
              cases ge <;> cases gc <;> simp
              have := IsEmpty.false p; contradiction

def countSucc
  (p : Parser ε ⟨ge, gc⟩ α)
  : (n : Nat) → Parser ε ⟨ge, gc⟩ (List.Vector α (n + 1))
  | 0 => (· ::ᵥ .nil) <$>ᵍ p
  | n + 1 => gdo
      let x ← p
      let rest ← countSucc p n
      return (x ::ᵥ rest)
      grade_by by simp

def count
  (p : Parser ε ⟨ge, gc⟩ α)
  : (n : Nat) → Parser ε ⟨ge ⊓ .possibly, gc ⊓ .possibly⟩ (List.Vector α n)
  | 0 => ok .nil
  | n + 1 => countSucc p n |>.relax

def sepByN
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  : (n : Nat) → Parser ε .fallible (List.Vector α n)
  | 0 => ok .nil
  | n + 1 => (gdo
    let sepP : Parser ε ⟨ge' ⊔ ge, gc' ⊔ gc⟩ α := gdo
      sep; p
      grade_by by simp
    let p1 ← p
    let ps ← count sepP n
    return (p1 ::ᵥ ps)) |>.weaken

def chainl1
  (op : Parser ε ⟨ge', .always⟩ (α → α → α))
  (p : Parser ε ⟨ge, .always⟩ α)
  : Parser ε ⟨ge, .always⟩ α := gdo
  let x ← p
  let rest ← many (gdo
    let f ← op
    let y ← p
    return (f, y))
  return rest.foldl (fun acc ⟨f, y⟩ => f acc y) x
  grade_by by simp

def fix [Inhabited ε]
  (f : Parser ε ⟨ge, .always⟩ α → Parser ε ⟨ge, .always⟩ α)
  (h : .possibly ≤ ge := by simp)
  : Parser ε ⟨ge, .always⟩ α :=
 let rec go {n} (t : Text n) : Outcome ε n ⟨ge, .always⟩ α :=
  match n, t with
  | 0, _ => Outcome.throw (h := h) default
  | n + 1, t =>
    let self : Parser ε ⟨ge, .always⟩ α :=
      ⟨fun {k} t' =>
        if k ≤ n then go t'
        else Outcome.throw (h := h) default⟩
    f self |>.run t
  ⟨fun {n} t => go t⟩

def eof : Parser Error .lookahead PUnit where
  run {n} t := match n with
   | .zero => ok () |>.run t
   | _ => throw Error.fail |>.run t

def lookahead (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge, .never⟩ α where
  run t := p.run t |>.handle
    (fun h e => Outcome.throw (h := h) e)
    (fun h r => Outcome.ofSuccess (c := h) {result := r.result, restText := t})

def notFollowedBy (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge.complement, .never⟩ PUnit where
  run t := p.run t |>.handle
    (fun _ _ => Outcome.ofSuccess (c := by cases ge <;> first | contradiction | decide) {result := (), restText := t})
    (fun _ _ => Outcome.throw (h := by cases ge <;> first | contradiction | decide) Error.fail)

-- Runs `p`. If `p` fails with error `e`, runs `recover e`. If recovery also
-- fails, reports `p`'s original error
def withRecovery
  (recover : ε' → Parser ε ⟨ge, gc⟩ α)
  (p : Parser ε' ⟨ge', gc'⟩ α)
  : Parser ε' ⟨ge ⊓ ge', ge'.ite gc gc'⟩ α where
  run t := p.run t |>.handle
    (fun h e => recover e |>.run t |>.handle
      (fun h' _ => Outcome.throw (h := by grind) e)
      (fun h' r => Outcome.ofSuccess (c := by grind)
        { r with witness := consumptionWitness.ite_right h r.witness }))
    (fun h r => Outcome.ofSuccess (c := by grind)
      { r with witness := consumptionWitness.ite_left h r.witness })

end Parser
