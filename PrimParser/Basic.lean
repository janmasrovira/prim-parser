import PrimParser.Base
import PrimParser.Necessity
import PrimParser.GradedMonad

abbrev Error := String
abbrev Text (n : Nat) := List.Vector Char n

structure Grade where
  errors : Necessity
  consumes : Necessity

namespace Grade

-- No parser can always consume and never fail, because it must accept empty
-- input
abbrev impossible : Grade where
  consumes := .always
  errors := .never

abbrev conditional : Grade where
  consumes := .always
  errors := .possibly

abbrev sink : Grade where
  consumes := .always
  errors := .always

abbrev flexible : Grade where
  consumes := .possibly
  errors := .never

abbrev fallible : Grade where
  consumes := .possibly
  errors := .possibly

abbrev failing : Grade where
  consumes := .possibly
  errors := .always

abbrev pure : Grade where
  consumes := .never
  errors := .never

abbrev lookahead : Grade where
  consumes := .never
  errors := .possibly

abbrev empty : Grade where
  consumes := .never
  errors := .always

instance : Monoid Grade where
  mul a b := ⟨a.errors ⊔ b.errors, a.consumes ⊔ b.consumes⟩
  mul_assoc a b c := by cases a; cases b; simp [HMul.hMul, Mul.mul]; grind
  one := pure
  one_mul a := by cases a; simp [HMul.hMul, Mul.mul, OfNat.ofNat, pure]
  mul_one a := by cases a; simp [HMul.hMul, Mul.mul, OfNat.ofNat, pure]

instance : Zero Grade where
  zero := empty

def add (a b : Grade) : Grade where
  errors := a.errors ⊓ b.errors
  consumes := a.consumes ⊔ b.consumes

instance : Add Grade where
  add := add

def natMul : Nat → Grade → Grade
  | 0, _ => 0
  | (m + 1), g => natMul m g + g

instance : AddMonoid Grade where
  zero := empty
  add_zero := by intro ⟨ge, gc⟩; simp [Add.add, add, HAdd.hAdd, OfNat.ofNat]
  zero_add := by intro ⟨ge, gc⟩; simp [Add.add, add, HAdd.hAdd, OfNat.ofNat]
  add_assoc := by intro ⟨ge1, gc1⟩ ⟨ge2, gc2⟩ ⟨ge3, gc3⟩
                  cases ge1 <;> cases gc1 <;> cases ge2 <;> cases gc2 <;>
                    simp [Add.add, add, HAdd.hAdd]
  nsmul := natMul
  nsmul_zero := by intro ⟨ge, gc⟩; simp [natMul, OfNat.ofNat, Zero.zero]
  nsmul_succ := by intro n ⟨ge, gc⟩; simp [natMul]

end Grade

namespace Parser

variable
  {n m : Nat}
  {a : Necessity}

abbrev consumptionWitness (n m : Nat) : Necessity → Prop
  | .always => n < m
  | .possibly => n ≤ m
  | .never => n = m

@[simp] theorem consumptionWitness.rfl : a ≤ .possibly → consumptionWitness n n a := by
  intro _; cases a <;> try simp
  contradiction

theorem consumptionWitness.min_possibly : consumptionWitness n m a → consumptionWitness n m (.possibly ⊓ a) := by
  cases a <;> grind only [Nat.le_of_succ_le]

structure Result (n : Nat) (consumes : Necessity) (α : Type) where
  result : α
  {restSize : Nat}
  restText : Text restSize
  witness : consumptionWitness restSize n consumes := by simp

abbrev Outcome (ε : Type) (n : Nat) (g : Grade) (α : Type) : Type :=
  match g.errors with
  | .never => Result n g.consumes α
  | .possibly => ε ⊕ Result n g.consumes α
  | .always => ε

end Parser

structure Parser (ε : Type) (g : Grade) (α : Type) where
  run : ∀ {n}, Text n → Parser.Outcome ε n g α

namespace Parser

variable
  {α β ε ε' : Type}
  {n m : Nat}
  {g g' : Grade}
  {ge ge' : Necessity} -- used for `errors`
  {gc gc': Necessity} -- used for `consumes`

def Outcome.handle
  (p : Outcome ε n ⟨ge, gc⟩ α)
  (e : .possibly ≤ ge → ε → β)
  (s : ge ≤ .possibly → Result n gc α → β)
  : β :=
  match ge with
  | .always => e (by decide) p
  | .never => s (by decide) p
  | .possibly => match p with
    | .inl x => e (by decide) x
    | .inr x => s (by decide) x

instance : Functor (Result n gc) where
  map f x := {x with result := f x.result}

instance : GFunctor (Result n) where
  gmap := Functor.map

instance : Functor (Outcome ε n g) where
  map f x := match g with
    | ⟨e, _⟩ => match e with
     | .never => by dsimp! at x ⊢; exact f <$> x
     | .possibly => by dsimp! at x ⊢; exact (Functor.map f) <$> x
     | .always => x

def Error.eof : Error := "eof"
def Error.fail : Error := "fail"

def Result.ap
  (r1 : Result n gc (α → β))
  (r2 : Result r1.restSize gc' α)
  : Result n (gc * gc') β where
  result := r1.result r2.result
  restSize := r2.restSize
  restText := r2.restText
  witness := by
    have w1 := r1.witness
    have w2 := r2.witness
    cases gc <;> cases gc' <;> omega

def Result.ap'
  (r1 : Result n gc α)
  (r2 : Result r1.restSize gc' (α → β))
  : Result n (gc * gc') β where
  result := r2.result r1.result
  restSize := r2.restSize
  restText := r2.restText
  witness := by
    have w1 := r1.witness
    have w2 := r2.witness
    cases gc <;> cases gc' <;> omega

def Result.seq
  (r1 : Result n gc α)
  (r2 : Result r1.restSize gc' β)
  : Result n (gc * gc') β where
  result := r2.result
  restSize := r2.restSize
  restText := r2.restText
  witness := by
    have w1 := r1.witness
    have w2 := r2.witness
    cases gc <;> cases gc' <;> omega

def Result.bindParser {xc fe fc : Necessity}
  (x : Result n xc α)
  (f : α → Parser ε ⟨fe, fc⟩ β)
  : Outcome ε n ⟨fe, xc * fc⟩ β :=
  match fe with
  | .always => (f x.result).run x.restText
  | .never => x.seq ((f x.result).run x.restText)
  | .possibly => match (f x.result).run x.restText with
    | .inr y => .inr (x.seq y)
    | .inl e => .inl e

instance : GFunctor (Parser ε) where
  gmap f p := ⟨fun t => f <$> p.run t⟩

def Outcome.throw (e : ε) (c : .possibly ≤ g.errors := by simp) : Outcome ε n g α := by
  rcases g with ⟨g1, g2⟩
  match h : g1 with
  | .possibly => exact .inl e
  | .always => exact e
  | .never => contradiction

def Outcome.ofResult (r : Result n gc α) (c : ge ≤ .possibly := by decide) : Outcome ε n ⟨ge, gc⟩ α :=
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

instance : GApplicative (Parser ε) where
  gpure a := ⟨fun t => ⟨a, t, rfl⟩⟩
  gseq f g := bind f fun f' => ⟨fun t => f' <$> (g ()).run t⟩

instance : GMonad (Parser ε) where
  gbind := bind

instance : LawfulFunctor (Result n gc) where
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

instance : LawfulGFunctor (Result n) where
  gmap_id x := by cases x; rfl
  gmap_comp g h x := by cases x; rfl

instance : LawfulGFunctor (Parser ε) where
  gmap_comp := by intro g _ _ _ f h p; simp [GFunctor.gmap]; ext n t; congr
  gmap_id := by intro g α ⟨p⟩; simp [GFunctor.gmap]

instance : LawfulGApplicative (Parser ε) where
  gmap_gpure := by intro _ _ _ _; congr
  gpure_gseq := by
    intro ⟨ge, gc⟩ α β f ⟨p⟩
    simp [GFunctor.gmap, GApplicative.gseq, bind, gpure]
    ext n t
    simp [Result.bindParser]
    cases ge <;> simp
    · cases p t <;> simp [Functor.map, Sum.bind, Result.seq]
    · cases p t; simp [Functor.map, Result.seq]

  gseq_gpure := by
    intro ⟨ge, gc⟩ α β ⟨p⟩ a
    cases ge <;> cases gc <;> simp [GFunctor.gmap, GApplicative.gseq, bind, gpure] <;> funext n t
      <;> simp [Functor.map, Result.bindParser, Result.seq, Outcome.throw, Sum.bind]
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
        · cases p1 t1 <;> simp [Outcome.throw, Result.bindParser]
          · cases ge3 <;> simp <;> congr 2 <;> apply max_assoc
          · next v =>
            cases ge3 <;> simp
            · case possibly =>
              cases p2 (Result.restText v) <;> simp [Result.seq]
              · congr 2; apply max_assoc
              · next v =>
                cases p3 (Result.restText v) <;> simp
                · congr 2; apply max_assoc
                · congr 2
                  · apply max_assoc
                  · apply max_assoc
                  · apply proof_irrel_heq
            · case always => cases p2 (Result.restText v) <;> simp [Result.seq]
            · case never =>
              cases p2 (Result.restText v) <;> simp [Result.seq]
              · congr 2; apply max_assoc
              · congr 2
                · apply max_assoc
                · apply max_assoc
                · apply proof_irrel_heq
        · cases p1 t1 <;> simp [Outcome.throw, Result.bindParser]
        · cases p1 t1 <;> simp [Outcome.throw, Result.bindParser]
          · cases ge3 <;> simp <;> congr 2 <;> apply max_assoc
          · next v =>
            cases ge3 <;> simp [Result.seq]
            · case possibly =>
              cases p3 (Result.restText (p2 (Result.restText v))) <;> simp
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
        simp [max]
        cases ge2 <;> simp
        · case possibly =>
          refine Function.hfunext rfl ?_; intro _ _ .rfl
          refine Function.hfunext rfl ?_; intro t1 t2 .rfl
          simp [GFunctor.gmap, Functor.map, Result.bindParser, Sum.bind, Result.seq]
          cases ge3 <;> simp
          · case possibly =>
            cases p2 (Result.restText (p1 t1)) <;> simp [Outcome.throw]
            · congr 2; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
            · next v =>
              cases p3 (Result.restText v) <;> simp
                <;> congr 2 <;> cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
          · case always =>
            cases p2 (Result.restText (p1 t1)) <;> simp
            · rfl
          · case never =>
            cases p2 (Result.restText (p1 t1)) <;> simp [Outcome.throw]
            · congr 2; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
            · congr 2 <;> · cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
        · case always => ext n a; simp [GFunctor.gmap, Functor.map, Result.bindParser]
        · case never =>
          cases ge3
          · case possibly =>
            refine Function.hfunext rfl ?_; intro _ _ .rfl
            refine Function.hfunext rfl ?_; intro t1 t2 .rfl
            simp [GFunctor.gmap, Functor.map, Result.bindParser, Sum.bind, Result.seq]
            cases p3 (Result.restText (p2 (Result.restText (p1 t1)))) <;> simp
            · congr 1; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
            · congr 1 <;> cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
          · case always =>
            simp [GFunctor.gmap, Functor.map, Result.bindParser]
            ext n t; congr
          · case never =>
            simp [Result.bindParser, Result.seq, Functor.map, GFunctor.gmap]
            refine Function.hfunext rfl ?_; intro _ _ .rfl
            refine Function.hfunext rfl ?_; intro _ _ .rfl
            congr 1
            · cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
            · apply proof_irrel_heq

instance : LawfulGMonad (Parser ε) where
  gpure_gbind := by
    intro ⟨ge, gc⟩ _ _ a f
    cases ge <;> simp [gpure, gbind, bind, Result.bindParser, Result.seq] <;> try (rcases f a with ⟨run'⟩; simp)
    · ext n t; cases run' t; simp; congr 2
    · congr

  gbind_gpure := by
    intro ⟨ge, gc⟩ _ ⟨p⟩
    simp [gpure, gbind, bind]
    congr 1
    · simp [OfNat.ofNat, One.one, HMul.hMul, Mul.mul]
    · refine Function.hfunext rfl ?_; intro _ _ .rfl
      refine Function.hfunext rfl ?_; intro t _ .rfl
      cases ge <;> simp [Outcome.throw, Result.bindParser, Result.seq]
      · case possibly =>
        cases p t <;> simp
        · congr 2; simp [OfNat.ofNat, One.one]
        · congr 2
          · simp [OfNat.ofNat, One.one, HMul.hMul, Mul.mul]
          · simp [OfNat.ofNat, One.one, HMul.hMul, Mul.mul]
          · apply proof_irrel_heq
      · case never =>
        cases p t; simp
        congr
        · simp [OfNat.ofNat, One.one, HMul.hMul, Mul.mul]
        · apply proof_irrel_heq

  gbind_assoc := by
    intro ⟨ge1, gc1⟩ ⟨ge2, gc2⟩ ⟨ge3, gc3⟩ α β γ ⟨p⟩ f g
    cases ge1
    · case possibly =>
      simp [gbind, bind]
      congr 1
      · grind
      · simp [HMul.hMul, Mul.mul]
        refine Function.hfunext rfl ?_; intro _ _ .rfl
        refine Function.hfunext rfl ?_; intro t _ .rfl
        cases ge2 <;> simp
        · cases p t <;> simp [Outcome.throw, Result.bindParser]
          · cases ge3 <;> simp <;> congr 2 <;> apply max_assoc
          · next v =>
            cases ge3 <;> simp
            · cases f v.result |>.run v.restText <;> simp [Result.seq]
              · congr 2; apply max_assoc
              · next v =>
                cases g v.result |>.run v.restText <;> simp
                · congr 2; apply max_assoc
                · congr 2
                  · apply max_assoc
                  · apply max_assoc
                  · apply proof_irrel_heq
            · cases f v.result |>.run v.restText <;> simp [Result.seq]
            · cases f v.result |>.run v.restText <;> simp [Result.seq]
              · congr 2; apply max_assoc
              · congr 2
                · apply max_assoc
                · apply max_assoc
                · apply proof_irrel_heq
        · cases p t <;> simp [Outcome.throw, Result.bindParser]
        · cases p t <;> simp [Outcome.throw, Result.bindParser]
          · cases ge3 <;> simp <;> congr 2 <;> apply max_assoc
          · next v =>
            cases ge3 <;> simp [Result.seq]
            · case possibly =>
              cases g (f v.result |>.run v.restText).result |>.run
                (f v.result |>.run v.restText).restText <;> simp
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
          simp [Result.bindParser, Result.seq]
          cases ge3 <;> simp
          · case possibly =>
            cases f (p t).result |>.run (p t).restText <;> simp [Outcome.throw]
            · congr 2; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
            · next v =>
              cases g v.result |>.run v.restText <;> simp
                <;> congr 2 <;> cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
          · case always =>
            cases f (p t).result |>.run (p t).restText <;> simp
            · rfl
          · case never =>
            cases f (p t).result |>.run (p t).restText <;> simp [Outcome.throw]
            · congr 2; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
            · congr 2 <;> · cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
        · case always => ext n a; simp [Result.bindParser]
        · case never =>
          cases ge3
          · case possibly =>
            refine Function.hfunext rfl ?_; intro _ _ .rfl
            refine Function.hfunext rfl ?_; intro t _ .rfl
            simp [Result.bindParser, Result.seq]
            cases g (f (p t).result |>.run (p t).restText).result |>.run
              (f (p t).result |>.run (p t).restText).restText <;> simp
            · congr 1; cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
            · congr 1 <;> cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
          · case always =>
            simp [Result.bindParser, Result.seq]
          · case never =>
            simp [Result.bindParser, Result.seq]
            refine Function.hfunext rfl ?_; intro _ _ .rfl
            refine Function.hfunext rfl ?_; intro _ _ .rfl
            congr 1
            · cases gc1 <;> cases gc2 <;> cases gc3 <;> simp [HMul.hMul, Mul.mul]
            · apply proof_irrel_heq

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
  (p1 : Parser Error ⟨ge, gc⟩ α)
  (p2 : Parser Error ⟨ge', gc'⟩ α)
  : Parser Error ⟨ge ⊓ ge', ge.ite gc' gc⟩ α where
  run t := match ge with
    | .never => Eq.mp (by simp) (p1.run t)
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

def Result.weakenConsumes (p : Result n gc α) : Result n .possibly α :=
  match gc with
  | .never => { p with witness := le_of_eq p.witness }
  | .possibly => p
  | .always => { p with witness := le_of_lt p.witness }

def Outcome.weakenConsumes (p : Outcome ε n ⟨ge, gc⟩ α) : Outcome ε n ⟨ge, .possibly⟩ α :=
  p.handle
    (fun c e => Outcome.throw (c := c) e)
    (fun c r => Outcome.ofResult (c := c) r.weakenConsumes)

def weakenErrors (p : Parser ε ⟨.never, gc⟩ α) : Parser ε ⟨.possibly, gc⟩ α where
  run t := .inr (p.run t)

def runOption (p : Parser ε ⟨ge, gc⟩ α) (t : Text n) : Option (Result n gc α) :=
  p.run t |>.handle (fun _ _ => .none) (fun _ r => .some r)

def char : Parser Error .conditional Char where
  run {n} t :=
    match n, t with
    | 0, .nil => .inl Error.eof
    | Nat.succ n, ⟨c :: cs, p⟩ =>
      .inr {result := c
            restSize := n
            restText := by refine ⟨cs, by simpa [List.length_cons] using p⟩
            witness := by simp}

def throw (e : ε) (c : .possibly ≤ g.errors := by simp) : Parser ε g α where
  run _ := Outcome.throw (c := c) e

-- Like `gpure` - it never consumes, it never errors - but with errors = .possibly
--  instead of .never. This allows `ok` to unify with fallible parsers
-- (e.g. `throw`) in match branches
def ok (a : α) : Parser ε ⟨.possibly, .never⟩ α := weakenErrors (gpure a)

def token (f : Char → Option α) : Parser Error .conditional α := gdo
  let c ← char
  match f c with
  | .some r => ok r
  | .none => throw Error.fail

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

private def many.go {n} (p : Parser ε ⟨ge, .always⟩ α) (t : Text n)
  : Result n .possibly (List α) :=
  match p.runOption t with
  | .none => {result := [], restText := t}
  | .some r =>
    have : r.restSize < n := r.witness
    let rest := many.go p r.restText
    {result := r.result :: rest.result
     restText := rest.restText
     witness := by have := rest.witness; omega}

def many (p : Parser ε ⟨ge, .always⟩ α) : Parser ε .flexible (List α) where
  run := many.go p

def many1 (p : Parser ε ⟨ge, .always⟩ α) : Parser ε ⟨ge, .always⟩ (List α) := by
  simpa [HMul.hMul, Mul.mul, OfNat.ofNat, One.one]
  using gdo
        let x ← p
        let xs ← many p
        return (x :: xs)

def eof : Parser Error .lookahead PUnit where
  run {n} t := match n with
   | .zero => ok () |>.run t
   | _ => throw Error.fail |>.run t

def lookahead (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge, .never⟩ α where
  run t := p.run t |>.handle
    (fun h e => Outcome.throw (c := h) e)
    (fun h r => Outcome.ofResult (c := h) {result := r.result, restText := t})

def notFollowedBy (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge.complement, .never⟩ PUnit where
  run t := p.run t |>.handle
    (fun _ _ => Outcome.ofResult (c := by cases ge <;> first | contradiction | decide) {result := (), restText := t})
    (fun _ _ => Outcome.throw (c := by cases ge <;> first | contradiction | decide) Error.fail)

-- Runs `p`. If `p` fails with error `e`, runs `recover e`. If recovery also
-- fails, reports `p`'s original error
def withRecovery
  (recover : ε' → Parser ε ⟨ge, gc⟩ α)
  (p : Parser ε' ⟨ge', gc'⟩ α)
  : Parser ε' ⟨ge ⊓ ge', ge'.ite gc gc'⟩ α where
  run t := p.run t |>.handle
    (fun h e => recover e |>.run t |>.handle
      (fun h' _ => Outcome.throw (c := by grind) e)
      (fun h' r => Outcome.ofResult (c := by grind)
        { r with witness := consumptionWitness.ite_right h r.witness }))
    (fun h r => Outcome.ofResult (c := by grind)
      { r with witness := consumptionWitness.ite_left h r.witness })

end Parser
