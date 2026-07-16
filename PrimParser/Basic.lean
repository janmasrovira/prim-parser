import PrimParser.Base
import PrimParser.Necessity
import PrimParser.GradedMonad

/-!
# PrimParser

A parser combinator library with precise grades tracking error and consumption
behavior at the type level via `Necessity`.
-/

abbrev Error := String

/-- Input text of statically known length `n`. -/
abbrev Text (n : Nat) := List.Vector Char n

/-- A parser's static grade: whether it may/must produce errors and
whether it may/must consume input. -/
structure Grade where
  errors : Necessity
  consumes : Necessity
  deriving Repr

namespace Grade

-- No parser can always consume and never fail, because it must accept empty
-- input
abbrev impossible : Grade where
  consumes := always
  errors := never

abbrev conditional : Grade where
  consumes := always
  errors := possibly

abbrev flexible : Grade where
  consumes := possibly
  errors := never

abbrev fallible : Grade where
  consumes := possibly
  errors := possibly

abbrev pure : Grade where
  consumes := never
  errors := never

abbrev lookahead : Grade where
  consumes := never
  errors := possibly

abbrev empty : Grade where
  consumes := never
  errors := always

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

@[simp] theorem one_mk : (1 : Grade) = ⟨never, never⟩ := by
  simp [OfNat.ofNat, One.one]

@[simp] theorem mul_idem (g : Grade) : g * g = g := by cases g; simp

def choice (a b : Grade) : Grade where
  errors := a.errors ⊓ b.errors
  consumes := a.errors.ite b.consumes a.consumes

end Grade

export Grade (impossible conditional flexible fallible pure lookahead empty)

namespace Parser

variable
  {n m : Nat}
  {a gc gc' : Necessity}
  {ε : Type}

/-- Relates input size `n` and remaining size `m` according to a consumption grade:
`always` requires strict decrease, `possibly` allows `≤`, `never` requires equality. -/
abbrev consumptionWitness (n m : Nat) : Necessity → Prop
  | always => n < m
  | possibly => n ≤ m
  | never => n = m

@[simp] theorem consumptionWitness.rfl : a ≤ possibly → consumptionWitness n n a := by
  intro _; cases a <;> try simp
  contradiction

theorem consumptionWitness.le : consumptionWitness n m a → n ≤ m := by
  cases a <;> simp_all; omega

theorem consumptionWitness.min_possibly : consumptionWitness n m a → consumptionWitness n m (possibly ⊓ a) := by
  cases a <;> grind only [Nat.le_of_succ_le]

theorem consumptionWitness.trans {n1 n2 n3 : Nat}
  (w1 : consumptionWitness n2 n1 gc)
  (w2 : consumptionWitness n3 n2 gc')
  : consumptionWitness n3 n1 (gc ⊔ gc') := by cases gc <;> cases gc' <;> omega

/-- A successful parse result -/
structure Success (n : Nat) (consumes : Necessity) (α : Type) where
  result : α
  {restSize : Nat}
  restText : Text restSize
  witness : consumptionWitness restSize n consumes := by simp

/-- A failed parse result -/
structure Failure (n : Nat) (ε : Type) where
  error : ε
  {restSize : Nat}
  restText : Text restSize
  witness : restSize ≤ n := by simp

def Failure.trans (f : Failure m ε) (h : m ≤ n) : Failure n ε where
  error := f.error
  restSize := f.restSize
  restText := f.restText
  witness := Nat.le_trans f.witness h

@[simp] def Failure.trans_rfl (f : Failure n ε) : f.trans (by simp) = f := by
  simp [trans]

/-- The result type of running a parser -/
abbrev Outcome (ε : Type) (n : Nat) (g : Grade) (α : Type) : Type :=
  Failure n ε ⊕ Success n g.consumes α

abbrev Outcome.Sound {g : Grade} {α : Type} (o : Outcome ε n g α) : Prop :=
  match o with
  | .inl _ => possibly ≤ g.errors
  | .inr _ => g.errors ≤ possibly

end Parser

/-- A parser with error type `ε`, static grade `g`, and result type `α`.
The grade tracks error and consumption behavior at the type level. -/
structure Parser (ε : Type) (g : Grade) (α : Type) where
  run : ∀ {n}, Text n → Parser.Outcome ε n g α
  sound : ∀ {n} (t : Text n), Parser.Outcome.Sound (run t)

namespace Parser

variable
  {α β γ ε ε' : Type}
  {n m : Nat}
  {g g' : Grade}
  {ge ge' : Necessity} -- used for `errors`
  {gc gc': Necessity} -- used for `consumes`

@[inline] def Outcome.handle
  (o : Outcome ε n g α)
  (sound : Sound o)
  (onError : possibly ≤ g.errors → Failure n ε → β)
  (onSuccess : g.errors ≤ possibly → Success n g.consumes α → β)
  : β :=
  match o with
  | .inl f => onError sound f
  | .inr r => onSuccess sound r

theorem Outcome.handle_sound
  {o : Outcome ε n g α}
  (sound : Sound o)
  (onError : possibly ≤ g.errors → Failure n ε → Outcome ε' m g' β)
  (onSuccess : g.errors ≤ possibly → Success n g.consumes α → Outcome ε' m g' β)
  (he : ∀ h f, Sound (onError h f))
  (hs : ∀ h r, Sound (onSuccess h r))
  : Sound (o.handle sound onError onSuccess) :=
  match o with
  | .inl f => he sound f
  | .inr r => hs sound r

instance : Functor (Success n gc) where
  map f x := {x with result := f x.result}

instance : GradedFunctor (Success n) where
  gmap := Functor.map

instance : Functor (Outcome ε n g) where
  map f o := match o with
    | .inl e => .inl e
    | .inr r => .inr (f <$> r)

theorem Outcome.map_sound (f : α → β) (o : Outcome ε n g α) (ho : Sound o)
  : Sound (f <$> o) := by
  cases o <;> simpa using ho

def Error.eof : Error := "eof"
def Error.fail : Error := "fail"

def Success.le (p : Success n gc α) : p.restSize ≤ n :=
  match gc with
  | never => le_of_eq p.witness
  | possibly => p.witness
  | always => le_of_lt p.witness

def Success.weakenConsumes (p : Success n gc α) : Success n possibly α :=
  { p with witness := p.le }

def Success.trans (s : Success m gc α) (h : m ≤ n) : Success n (gc ⊔ possibly) α where
  result := s.result
  restSize := s.restSize
  restText := s.restText
  witness := by
    have w := s.witness
    cases gc <;> omega

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

@[inline] def Success.bindParser {xc fe fc : Necessity}
  (x : Success n xc α)
  (f : α → Parser ε ⟨fe, fc⟩ β)
  : Outcome ε n ⟨fe, xc ⊔ fc⟩ β :=
  match (f x.result).run x.restText with
  | .inl e => .inl (e.trans x.le)
  | .inr y => .inr (x.seq y)

instance : GradedFunctor (Parser ε) where
  gmap f p := {
    run t := f <$> p.run t
    sound t := Outcome.map_sound f (p.run t) (p.sound t)
  }

@[inline] def Outcome.throwFailure (f : Failure n ε) : Outcome ε n g α :=
  .inl f

theorem Outcome.throwFailure_sound {f : Failure n ε} (h : possibly ≤ g.errors)
  : Sound (Outcome.throwFailure (α := α) (g := g) f) := h

def Outcome.throw (e : ε) (t : Text n) : Outcome ε n g α :=
  Outcome.throwFailure { error := e, restText := t, witness := by simp }

theorem Outcome.throw_sound (e : ε) (t : Text n) (h : possibly ≤ g.errors)
  : Sound (Outcome.throw (α := α) (g := g) e t) := h

@[inline] def Outcome.ofSuccess (r : Success n gc α) : Outcome ε n ⟨ge, gc⟩ α :=
  .inr r

theorem Outcome.ofSuccess_sound {r : Success n gc α} (c : ge ≤ possibly)
  : Sound (Outcome.ofSuccess (ε := ε) (ge := ge) r) := c

@[inline] def onOutcome
  (p : Parser ε g α)
  (onError : ∀ {n}, Text n → possibly ≤ g.errors → Failure n ε → Outcome ε' n g' β)
  (onSuccess : ∀ {n}, Text n → g.errors ≤ possibly → Success n g.consumes α → Outcome ε' n g' β)
  (he : ∀ {n} (t : Text n) h f, Outcome.Sound (onError t h f))
  (hs : ∀ {n} (t : Text n) h r, Outcome.Sound (onSuccess t h r))
  : Parser ε' g' β where
  run t := (p.run t).handle (p.sound t) (onError t) (onSuccess t)
  sound t := Outcome.handle_sound (p.sound t) (onError t) (onSuccess t) (he t) (hs t)

/-- Monadic bind for parsers. The resulting grade is the product (max)
of the two grades. -/
def bind
  (m : Parser ε g α)
  (f : α → Parser ε g' β)
  : Parser ε (g * g') β where
  run t := match m.run t with
    | .inl e => .inl e
    | .inr x => match f x.result |>.run x.restText with
      | .inl e => .inl (e.trans x.le)
      | .inr y => .inr (x.seq y)
  sound t := by
    rcases g with ⟨ge, gc⟩; rcases g' with ⟨ge', gc'⟩
    have hm := m.sound t
    cases hmr : m.run t with
    | inl e =>
      simp only [hmr] at hm
      exact le_sup_of_le_left hm
    | inr x =>
      have hf := f x.result |>.sound x.restText
      cases hfr : f x.result |>.run x.restText with
      | inl e =>
        simp only [hfr] at hf ⊢
        exact le_sup_of_le_right hf
      | inr y =>
        simp only [hmr, hfr] at hf hm ⊢
        exact sup_le hm hf

instance : IsEmpty (Parser ε impossible α) where
  false p := by
    have h := p.sound (⟨[], rfl⟩ : Text 0)
    cases hr : p.run (⟨[], rfl⟩ : Text 0) with
    | inl f => rw [hr] at h; contradiction
    | inr s => have := s.witness; omega

/-- Lift a value into a parser that consumes nothing and never fails. -/
abbrev pure (a : α) : Parser ε 1 α where
  run t := Outcome.ofSuccess (ge := never) { result := a, restText := t, witness := rfl }
  sound t := Outcome.ofSuccess_sound (by decide)

instance : GradedApplicative (Parser ε) where
  gpure := pure
  gseq f g := bind f fun f' =>
    { run := fun t => f' <$> (g ()).run t
      sound := fun t => Outcome.map_sound f' ((g ()).run t) ((g ()).sound t) }

instance : GradedMonad (Parser ε) where
  gbind := bind

-- `Inhabited ε` is needed to throw a `default` error on empty input
private def fixGo [Inhabited ε]
    (h : possibly ≤ ge)
    (f : Parser ε ⟨ge, always⟩ α → Parser ε ⟨ge, always⟩ α)
    (n : Nat)
    (t : Text n)
    : {o : Outcome ε n ⟨ge, always⟩ α // Outcome.Sound o} :=
  match n, t with
  | 0, t => ⟨Outcome.throw default t, Outcome.throw_sound _ _ h⟩
  | m + 1, t =>
    let self : Parser ε ⟨ge, always⟩ α :=
      { run := fun {k} t' =>
          if hk : k ≤ m then fixGo h f k t' |>.val
          else Outcome.throw default t'
        sound := fun {k} t' => by
          split
          · exact fixGo h f k t' |>.property
          · exact Outcome.throw_sound _ _ h }
    ⟨f self |>.run t, f self |>.sound t⟩

/-- Build a recursive parser via a fixpoint. Termination is guaranteed by
requiring the body to always consume input. -/
def fix [Inhabited ε]
  (f : Parser ε ⟨ge, always⟩ α → Parser ε ⟨ge, always⟩ α)
  (h : possibly ≤ ge := by simp)
  : Parser ε ⟨ge, always⟩ α :=
  { run := fun t => fixGo h f _ t |>.val
    sound := fun t => fixGo h f _ t |>.property }

private theorem consumptionWitness.ite_right
  (c : possibly ≤ ge')
  (w : consumptionWitness n m gc)
  : consumptionWitness n m (ge'.ite gc gc') := by
  cases ge' <;> cases gc <;> cases gc' <;> first | contradiction | simp; omega

private theorem consumptionWitness.ite_left
  (c : ge' ≤ possibly)
  (w : consumptionWitness n m gc')
  : consumptionWitness n m (ge'.ite gc gc') := by
  cases ge' <;> cases gc <;> cases gc' <;> first | contradiction | simp; omega

/-- Run `p`. If it fails, restores the original text. -/
def withBacktracking {g} (p : Parser ε g α) : Parser ε g α :=
  p.onOutcome
    (fun t _ f => Outcome.throwFailure { error := f.error, restText := t, witness := by simp })
    (fun _ _ s => Outcome.ofSuccess s)
    (fun _ h _ => Outcome.throwFailure_sound h)
    (fun _ h _ => Outcome.ofSuccess_sound h)

/-- Try `p1`; if it fails, try `p2`. The error grade is the infimum and
the consumption grade is computed via `Necessity.ite`. -/
def choice
  (p1 : Parser ε ⟨ge, gc⟩ α)
  (p2 : Parser ε ⟨ge', gc'⟩ α)
  -- TODO review 18 begin
  : Parser ε ⟨ge ⊓ ge', ge.ite gc' gc⟩ α :=
  p1.onOutcome
    (fun t hge _ =>
      p2.run t |>.handle (p2.sound t)
        (fun _ f' => Outcome.throwFailure f')
        (fun _ s' => Outcome.ofSuccess
          { s' with witness := consumptionWitness.ite_right hge s'.witness }))
    (fun _ hge s => Outcome.ofSuccess
      { s with witness := consumptionWitness.ite_left hge s.witness })
    (fun t hge _f => Outcome.handle_sound (p2.sound t) _ _
      (fun hge' _ => le_inf hge hge')
      (fun hge' _ => inf_le_right.trans hge'))
    (fun _ hge _ => inf_le_left.trans hge)
  -- TODO review 18 end

infixl:20 " <|> " => choice

/-- try `p1`; if it fails *without consuming*, then try `p2` -/
def committedChoice
  (p1 : Parser ε ⟨ge, gc⟩ α)
  (p2 : Parser ε ⟨ge', gc'⟩ α)
  -- TODO review 19 begin
  : Parser ε ⟨ge ⊓ (ge' ⊔ possibly), ge.ite gc' gc⟩ α :=
  p1.onOutcome
    (fun {n} t hge f =>
  -- TODO review 19 end
      if f.restSize = n then
        -- TODO review 20 begin
        p2.run t |>.handle (p2.sound t)
          (fun hge' f' => Outcome.throwFailure f')
          (fun hge' s' => Outcome.ofSuccess
            { s' with witness := consumptionWitness.ite_right hge s'.witness })
        -- TODO review 20 end
      else
        -- TODO review 21 begin
        Outcome.throwFailure f)
    (fun _ hge s => Outcome.ofSuccess
      { s with witness := consumptionWitness.ite_left hge s.witness })
    (fun {n} t hge f => by
      show Outcome.Sound (if f.restSize = n then _ else _)
      split
      · exact Outcome.handle_sound (p2.sound t) _ _
          (fun hge' _ => le_inf hge le_sup_right)
          (fun hge' _ => inf_le_right.trans (sup_le hge' le_rfl))
      · exact le_inf hge le_sup_right)
    (fun _ hge _ => inf_le_left.trans hge)
        -- TODO review 21 end

/-- Try `p1` first, if it fails with `Failure f`, run `p2` on `f.restText` -/
def tryResume
  (p1 : Parser ε ⟨ge, gc⟩ α)
  (p2 : Parser ε ⟨ge', gc'⟩ α)
  -- TODO review 22 begin
  : Parser ε ⟨ge ⊓ ge', ge.ite (gc' ⊔ possibly) gc⟩ α :=
  p1.onOutcome
    (fun _ hge f =>
      p2.run f.restText |>.handle (p2.sound f.restText)
        (fun _ f' => Outcome.throwFailure (f'.trans f.witness))
  -- TODO review 22 end
        (fun _ s' =>
          let lifted := s'.trans f.witness
          -- TODO review 23 begin
          Outcome.ofSuccess
          -- TODO review 23 end
            { lifted with witness := consumptionWitness.ite_right hge lifted.witness }))
    -- TODO review 24 begin
    (fun _ hge s => Outcome.ofSuccess
      { s with witness := consumptionWitness.ite_left hge s.witness })
    (fun _ hge f => Outcome.handle_sound (p2.sound f.restText) _ _
      (fun hge' _ => le_inf hge hge')
      (fun hge' _ => inf_le_right.trans hge'))
    (fun _ hge _ => inf_le_left.trans hge)
    -- TODO review 24 end

/-- Try each parser in the list in order, returning the first success. -/
def oneOf (l : NonEmptyList (Parser ε g α)) : Parser ε g α :=
  let rec go (l : List (Parser ε g α)) (p : l.length ≠ 0 := by simp) : Parser ε g α := match l with
      | [] => nomatch p
      | [x] => x
      | x :: y :: xs => by refine cast ?_ (choice x (go (y :: xs)))
                           congr 2 <;> simp
  go l.1 (p := by simpa using l.2)

/-- A parser that always fails with error `e`. -/
def throw (e : ε) (c : possibly ≤ ge := by simp) : Parser ε ⟨ge, gc⟩ α where
  run t := Outcome.throw e t
  -- TODO review 25 begin
  sound _t := Outcome.throw_sound _ _ c
  -- TODO review 25 end

def Success.relaxConsumes (p : Success n gc α) : Success n (gc ⊓ possibly) α :=
  match gc with
  | never => p
  | possibly => p
  | always => { p with witness := le_of_lt p.witness }

/-- Weaken the consumption grade by capping at `possibly`. -/
-- TODO review 26 begin
def relaxConsumes (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge, gc ⊓ possibly⟩ α :=
  p.onOutcome
    (fun _ _ f => Outcome.throwFailure f)
    (fun _ _ r => Outcome.ofSuccess r.relaxConsumes)
    (fun _ h _ => h)
    (fun _ h _ => h)
-- TODO review 26 end

/-- Weaken the error grade by capping at `possibly`. -/
-- TODO review 27 begin
def relaxErrors (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge ⊓ possibly, gc⟩ α :=
  p.onOutcome
    (fun _ _ f => Outcome.throwFailure f)
    (fun _ _ r => Outcome.ofSuccess r)
    (fun _ h _ => Outcome.throwFailure_sound (le_inf h le_rfl))
    (fun _ _ _ => Outcome.ofSuccess_sound inf_le_right)
-- TODO review 27 end

/-- Cap both error and consumption grades at `possibly`. -/
def relax (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge ⊓ possibly, gc ⊓ possibly⟩ α :=
  p.relaxErrors.relaxConsumes

/-- Forget consumption precision, setting it to `possibly`. -/
-- TODO review 28 begin
def weakenConsumes (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge, possibly⟩ α :=
  p.onOutcome
    (fun _ _ f => Outcome.throwFailure f)
    (fun _ _ r => Outcome.ofSuccess r.weakenConsumes)
    (fun _ h _ => h)
    (fun _ h _ => h)
-- TODO review 28 end

/-- Forget error precision, setting it to `possibly`. -/
-- TODO review 29 begin
def weakenErrors (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨possibly, gc⟩ α :=
  p.onOutcome
    (fun _ _ f => Outcome.throwFailure f)
    (fun _ _ r => Outcome.ofSuccess r)
    (fun _ _ _ => Outcome.throwFailure_sound (le_refl _))
    (fun _ _ _ => Outcome.ofSuccess_sound (le_refl _))
-- TODO review 29 end

/-- Weaken both grades to `possibly`, yielding a `fallible` parser. -/
def weaken (p : Parser ε ⟨ge, gc⟩ α) : Parser ε fallible α :=
  p.weakenErrors.weakenConsumes

/-- Run a parser, discarding the error and returning the `Success` as an `Option`. -/
def runOption (p : Parser ε ⟨ge, gc⟩ α) (t : Text n) : Option (Success n gc α) :=
  -- TODO review 30 begin
  p.run t |>.handle (p.sound t) (fun _ _ => .none) (fun _ r => .some r)
  -- TODO review 30 end

/-- Run a parser, returning only the parsed value as an `Option`. -/
def runResult? (p : Parser ε ⟨ge, gc⟩ α) (t : Text n) : Option α :=
  -- TODO review 31 begin
  p.run t |>.handle (p.sound t) (fun _ _ => .none) (fun _ r => .some r.result)

theorem Outcome.sound_of_errors_eq_possibly (o : Outcome ε n g α) (hg : g.errors = possibly)
  : Sound o := by cases o <;> simp [Outcome.Sound, hg]
  -- TODO review 31 end

/-- Consume and return a single character, or fail on empty input. -/
def anyChar : Parser Error conditional Char where
  run {n} t :=
    match n, t with
    | 0, .nil => .inl { error := Error.eof, restText := .nil, witness := by simp }
    | Nat.succ n, ⟨c :: cs, p⟩ =>
      .inr {result := c
            restSize := n
            restText := by refine ⟨cs, by simpa [List.length_cons] using p⟩
            witness := by simp}
  -- TODO review 32 begin
  sound t := Outcome.sound_of_errors_eq_possibly _ rfl
  -- TODO review 32 end

/-- Like `gpure` but with a flexible grade: both `ge` and `gc` can be `never`
or `possibly`. Useful in match branches where all cases must share the same grade. -/
def ok (a : α) (he : ge ≤ possibly := by simp) (hc : gc ≤ possibly := by simp)
  : Parser ε ⟨ge, gc⟩ α := match gc with
  | always => nomatch hc
  | possibly => weakenConsumes (match h : ge with
              | possibly => weakenErrors (gpure a)
              | never => gpure a
              | always => by rw [h] at he; contradiction)
  | never => match h : ge with
              | possibly => weakenErrors (gpure a)
              | never => gpure a

/-- Consume a character and apply `f`; succeed with the result or fail if `f` returns `none`. -/
def token (f : Char → Option α) : Parser Error conditional α := gdo
  let c ← anyChar
  match f c with
  | .some r => ok (gc := never) r
  | .none => throw (ge := possibly) Error.fail

/-- Consume a character that satisfies predicate `f`, or fail. -/
def satisfy (f : Char → Bool) : Parser Error conditional Char :=
  token (fun c => if f c then .some c else .none)

/-- Like `satisfy` but returns `PUnit`. -/
def skipSatisfy (f : Char → Bool) : Parser Error conditional PUnit :=
  () <$ᵍ satisfy f

/-- Match a specific character. -/
def char (c : Char) : Parser Error conditional PUnit :=
  skipSatisfy (· == c)

/-- Match an exact string. -/
def string (str : String) : Parser Error conditional PUnit :=
  let rec go : List Char → Parser Error conditional PUnit
    | [] => throw Error.fail
    | [c] => skipSatisfy (· == c)
    | c :: cs => gdo
      skipSatisfy (· == c)
      go cs
  go str.toList

/-- Try `p`; return `some result` on success or `none` on failure, never failing itself. -/
def optional (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨never, ge.complement ⊓ gc⟩ (Option α) where
  -- TODO review 33 begin
  run t := match ge, p.run t, p.sound t with
    | never, .inl _, hs => absurd hs (by decide : ¬ ((possibly : Necessity) ≤ never))
    | never, .inr r, _ =>
      .inr {result := .some r.result, restText := r.restText, witness := r.witness}
    | always, _, _ => .inr {result := .none, restText := t}
    | possibly, .inl _, _ => .inr {result := .none, restText := t}
    | possibly, .inr r, _ =>
      .inr {result := .some r.result, restText := r.restText, witness := r.witness.min_possibly}
  sound t := by
    match ge, p.run t, p.sound t with
    | never, .inl _, hs => exact absurd hs (by decide : ¬ ((possibly : Necessity) ≤ never))
    | never, .inr _, _ | always, _, _ | possibly, .inl _, _ | possibly, .inr _, _ =>
        exact (by decide : (Necessity.never) ≤ possibly)
  -- TODO review 33 end

/-- Try `p`; return the result on success or the default value `d` on failure. -/
def optionalD (p : Parser ε ⟨ge, gc⟩ α) (d : α) : Parser ε ⟨never, ge.complement ⊓ gc⟩ α :=
  (·.getD d) <$>ᵍ optional p

/-- Try `p` then apply `cont` to its result; wrap the final result in `Option`. -/
def optionalBind
  (p : Parser ε ⟨ge, gc⟩ α)
  (cont : α → Parser ε ⟨ge', gc'⟩ β)
  : Parser ε ⟨never, (ge ⊔ ge').complement ⊓ (gc ⊔ gc')⟩ (Option β) :=
  optional (gdo
    let a ← p
    cont a
    grade_by by simp)

def test (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨never, ge.complement ⊓ gc⟩ Bool :=
  Option.isSome <$>ᵍ optional p

/-- Repeatedly apply `p` until `e` succeeds, collecting the results of `p`. -/
def manyTill [Inhabited ε]
  (p : Parser ε ⟨ge, always⟩ α)
  (e : Parser ε ⟨ge', always⟩ β)
  : Parser ε ⟨ge, always⟩ (List α) :=
  match ge with
  | always => (fun x => [x]) <$>ᵍ p
  | never => IsEmpty.false p |>.elim
  | possibly =>
      fix fun self =>
        oneOf (
          ([] <$ᵍ e |>.weakenErrors) ::₁
          [gdo let a ← p; let as ← self; return (a :: as); grade_by by simp]
        )

/-- Apply `p` zero or more times, collecting results. Requires `p` to always consume. -/
def many (p : Parser ε ⟨ge, always⟩ α) : Parser ε flexible (List α) where
  run :=
    let rec go {n} (p : Parser ε ⟨ge, always⟩ α) (t : Text n)
        : Success n possibly (List α) :=
      match p.runOption t with
      | .none => {result := [], restText := t}
      | .some r =>
        have : r.restSize < n := r.witness
        let rest := go p r.restText
        {result := r.result :: rest.result
         restText := rest.restText
         witness := by have := rest.witness; omega}
    -- TODO review 34 begin
    fun t => Outcome.ofSuccess (ge := never) (go p t)
  sound t := Outcome.ofSuccess_sound (by decide)
    -- TODO review 34 end


/-- Apply `p` one or more times, collecting results. -/
def many1 (p : Parser ε ⟨ge, always⟩ α) : Parser ε ⟨ge, always⟩ (NonEmptyList α) := gdo
  let x ← p
  let xs ← many p
  return x ::₁ xs
  grade_by by simp

/-- Apply `p` zero or more times, discarding results. -/
def skipMany (p : Parser ε ⟨ge, always⟩ α) : Parser ε flexible PUnit :=
  () <$ᵍ many p

/-- Apply `p` one or more times, discarding results. -/
def skipMany1 (p : Parser ε ⟨ge, always⟩ α) : Parser ε ⟨ge, always⟩ PUnit :=
  () <$ᵍ many1 p

/-- Consume characters while `f` holds, returning the collected string. -/
def takeWhile (f : Char → Bool) : Parser Error flexible String :=
  String.ofList <$>ᵍ many (satisfy f)

/-- Consume one or more characters while `f` holds. -/
def takeWhile1 (f : Char → Bool) : Parser Error conditional String :=
  (String.ofList ∘ NonEmptyList.toList) <$>ᵍ many1 (satisfy f)

/-- Skip characters while `f` holds. -/
def skipWhile (f : Char → Bool) : Parser Error flexible PUnit :=
  () <$ᵍ takeWhile f

/-- Skip one or more characters while `f` holds. -/
def skipWhile1 (f : Char → Bool) : Parser Error conditional PUnit :=
  () <$ᵍ takeWhile1 f

/-- Skip zero or more whitespace characters. -/
def whitespace : Parser Error flexible PUnit :=
  skipWhile Char.isWhitespace

/-- Skip one or more whitespace characters. -/
def whitespace1 : Parser Error conditional PUnit :=
  skipWhile1 Char.isWhitespace

/-- Run `p` then skip trailing whitespace. -/
def lexeme (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge, gc ⊔ possibly⟩ α := gdo
  let r ← p
  whitespace
  return r
  grade_by by simp

def lparen   := char '('
def rparen   := char ')'
def lbracket := char '['
def rbracket := char ']'
def lbrace   := char '{'
def rbrace   := char '}'
def dquote   := char '\"'
def comma    := char ','

/-- Parse `p` surrounded by parentheses. -/
def parens (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge ⊔ possibly, always⟩ α := gdo
  lexeme lparen; let r ← p; lexeme rparen; return r
  grade_by by simp

/-- Parse `p` surrounded by square brackets. -/
def brackets (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge ⊔ possibly, always⟩ α := gdo
  lexeme lbracket; let r ← p; lexeme rbracket; return r
  grade_by by simp

/-- Parse `p` surrounded by curly braces. -/
def braces (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge ⊔ possibly, always⟩ α := gdo
  lexeme lbrace; let r ← p; lexeme rbrace; return r
  grade_by by simp

/-- Parse a single decimal digit, returning its numeric value. -/
def digit : Parser Error conditional Nat :=
  token fun c => if c.isDigit then some (c.toNat - '0'.toNat) else none

/-- Parse a natural number (one or more digits). -/
def nat : Parser Error conditional Nat := gdo
  let d ← digit
  let ds ← many digit
  return ds.foldl (fun acc d => acc * 10 + d) d

/-- Parse an integer (optional leading `-` followed by digits). -/
def int : Parser Error conditional Int := gdo
  let neg ← optional (char '-')
  let n ← nat
  return if neg.isSome then -n else n
  grade_by by simp

def space : Parser Error conditional PUnit := skipSatisfy (· == ' ')

def tab : Parser Error conditional PUnit := skipSatisfy (· == '\t')

namespace ASCII

def lf : Parser Error conditional PUnit := skipSatisfy (· == '\n')

def cr : Parser Error conditional PUnit := skipSatisfy (· == '\r')

/-- Match an ASCII uppercase letter. -/
def uppercase : Parser Error conditional Char := satisfy Char.isUpper

/-- Match an ASCII lowercase letter. -/
def lowercase : Parser Error conditional Char := satisfy Char.isLower

/-- Match an ASCII letter. -/
def alpha : Parser Error conditional Char := satisfy Char.isAlpha

/-- Match an ASCII letter or digit. -/
def alphanum : Parser Error conditional Char := satisfy Char.isAlphanum

/-- Match an ASCII control character. -/
def control : Parser Error conditional Char :=
  satisfy fun c => c.val < 0x20 || c.val == 0x7F

/-- Match a binary digit. -/
def binDigit : Parser Error conditional Bool :=
  token fun
    | '0' => some false
    | '1' => some true
    | _   => none

/-- Match an octal digit, returning its numeric value. -/
def octDigit : Parser Error conditional (Fin 8) :=
  token fun
    | '0' => some 0
    | '1' => some 1
    | '2' => some 2
    | '3' => some 3
    | '4' => some 4
    | '5' => some 5
    | '6' => some 6
    | '7' => some 7
    | _ => none

/-- Match a hexadecimal digit, returning its numeric value. -/
def hexDigit : Parser Error conditional (Fin 16) :=
  token fun
    | '0' => some 0
    | '1' => some 1
    | '2' => some 2
    | '3' => some 3
    | '4' => some 4
    | '5' => some 5
    | '6' => some 6
    | '7' => some 7
    | '8' => some 8
    | '9' => some 9
    | 'a' | 'A' => some 10
    | 'b' | 'B' => some 11
    | 'c' | 'C' => some 12
    | 'd' | 'D' => some 13
    | 'e' | 'E' => some 14
    | 'f' | 'F' => some 15
    | _ => none

end ASCII

/-- Match a line terminator: LF or CRLF. -/
def eol : Parser Error conditional PUnit := gdo
  optional ASCII.cr
  ASCII.lf
  grade_by by simp

/-- Parse zero or more occurrences of `p` separated by `sep`. -/
def sepBy
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  (h : gc' ⊔ gc = always := by simp)
  : Parser ε flexible (List α) := gdo
  let m ← optional p
  match m with
  | .some f =>
    let item : Parser ε ⟨ge' ⊔ ge, always⟩ α := gdo
        sep; p
        grade_by by simp [h]
    let rest ← many item
    ok (gc := possibly) (f :: rest)
  | .none => ok (ge := never) []
  grade_by by simp
              cases ge <;> cases gc <;> simp
              have := IsEmpty.false p; contradiction

/-- Parse one or more occurrences of `p` separated by `sep`. -/
def sepBy1
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  (h : gc' ⊔ gc = always := by simp)
  : Parser ε ⟨ge, gc ⊔ possibly⟩ (NonEmptyList α) := gdo
  let first ← p
  let item : Parser ε ⟨ge' ⊔ ge, always⟩ α := gdo
    sep; p
    grade_by by simp [h]
  let rest ← many item
  return first ::₁ rest
  grade_by by simp

/-- Parse zero or more occurrences of `p`, each followed by `sep`. -/
def endBy
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  (h : gc ⊔ gc' = always := by simp)
  : Parser ε flexible (List α) :=
  let item : Parser ε ⟨ge ⊔ ge', always⟩ α := gdo
    let x ← p; sep; return x
    grade_by by simp [h]
  many item

/-- Parse one or more occurrences of `p`, each followed by `sep`. -/
def endBy1
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  (h : gc ⊔ gc' = always := by simp)
  : Parser ε ⟨ge ⊔ ge', always⟩ (NonEmptyList α) :=
  let item : Parser ε ⟨ge ⊔ ge', always⟩ α := gdo
    let x ← p; sep; return x
    grade_by by simp [h]
  many1 item

/-- Parse one or more occurrences of `p` separated by `sep`, with an optional
trailing `sep`. -/
def sepEndBy1
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  (h : gc' ⊔ gc = always := by simp)
  : Parser ε ⟨ge, gc ⊔ possibly⟩ (NonEmptyList α) := gdo
  let xs ← sepBy1 sep p (h := h)
  weakenConsumes (optional sep)
  return xs
  grade_by by simp

/-- Parse zero or more occurrences of `p` separated by `sep`, with an optional
trailing `sep`. -/
def sepEndBy
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  (h : gc' ⊔ gc = always := by simp)
  : Parser ε flexible (List α) := gdo
  let xs ← sepBy sep p (h := h)
  weakenConsumes (optional sep)
  return xs
  grade_by by simp

/-- Parse exactly `n + 1` occurrences of `p`. -/
def count1
  (n : Nat)
  (p : Parser ε ⟨ge, gc⟩ α)
  : Parser ε ⟨ge, gc⟩ (List.Vector α (n + 1)) :=
  match n with
  | 0 => (· ::ᵥ .nil) <$>ᵍ p
  | n + 1 => gdo
      let x ← p
      let rest ← count1 n p
      return (x ::ᵥ rest)
      grade_by by simp

/-- Parse exactly `n` occurrences of `p`. -/
def count
  (n : Nat)
  (p : Parser ε ⟨ge, gc⟩ α)
  : Parser ε ⟨ge ⊓ possibly, gc ⊓ possibly⟩ (List.Vector α n) :=
  match n with
  | 0 => ok .nil
  | n + 1 => count1 n p |>.relax

/-- Skip exactly `n` occurrences of `p`. -/
def skip (n : Nat) (p : Parser ε ⟨ge, gc⟩ α)
  : Parser ε ⟨ge ⊓ possibly, gc ⊓ possibly⟩ PUnit :=
  () <$ᵍ count n p

/-- Skip up to `n` occurrences of `p`; never fails. -/
def skipUpTo : (n : Nat) → Parser ε ⟨ge, always⟩ α → Parser ε flexible PUnit
  | 0, _ => ok ()
  | n + 1, p => gdo
    let m ← weakenConsumes (optional p)
    match m with
    | .none => ok (ge := never) ()
    | .some _ => skipUpTo n p
    grade_by by simp

/-- Skip `n` or more occurrences of `p`. -/
def skipManyN (n : Nat) (p : Parser ε ⟨ge, always⟩ α)
  : Parser ε ⟨ge ⊓ possibly, possibly⟩ PUnit := gdo
  skip n p
  skipMany p
  grade_by by simp

/-- Run `p` until `stop` succeeds; discard `p`'s results. -/
def skipUntil [Inhabited ε]
  (stop : Parser ε ⟨ge', always⟩ β)
  (p : Parser ε ⟨ge, always⟩ α)
  : Parser ε ⟨ge, always⟩ PUnit :=
  () <$ᵍ manyTill p stop

/-- Parse exactly `n` occurrences of `p` separated by `sep`. -/
def sepByN
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  : (n : Nat) → Parser ε fallible (List.Vector α n)
  | 0 => ok .nil
  | n + 1 => (gdo
    let sepP : Parser ε ⟨ge' ⊔ ge, gc' ⊔ gc⟩ α := gdo
      sep; p
      grade_by by simp
    let p1 ← p
    let ps ← count n sepP
    return (p1 ::ᵥ ps)) |>.weaken

/-- Parse one or more occurrences of `p` separated by left-associative operator `op`. -/
def chainl1
  (op : Parser ε ⟨ge', always⟩ (α → α → α))
  (p : Parser ε ⟨ge, always⟩ α)
  : Parser ε ⟨ge, always⟩ α := gdo
  let x ← p
  let rest ← many (gdo
    let f ← op
    let y ← p
    return (f, y))
  return rest.foldl (fun acc ⟨f, y⟩ => f acc y) x
  grade_by by simp

/-- Succeed only at end of input, consuming nothing. -/
def eof : Parser Error lookahead PUnit where
  run {n} t := match n with
   | .zero => ok () |>.run t
   | _ => throw Error.fail |>.run t
  -- TODO review 35 begin
  sound t := Outcome.sound_of_errors_eq_possibly _ rfl
  -- TODO review 35 end

/-- Run `p` without consuming input, keeping only the result. -/
-- TODO review 36 begin
def lookahead (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge, never⟩ α :=
  p.onOutcome
    (fun _ h f => Outcome.throwFailure f)
    (fun t h r => Outcome.ofSuccess {result := r.result, restText := t})
    (fun _ h _ => h)
    (fun _ h _ => h)
-- TODO review 36 end

def peek : Parser Error Grade.lookahead Char := lookahead anyChar

/-- Succeed (without consuming) only when `p` fails. -/
-- TODO review 37 begin
def notFollowedBy (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge.complement, never⟩ PUnit :=
  p.onOutcome
    (fun t h _ => Outcome.ofSuccess {result := (), restText := t})
    (fun t h _ => Outcome.throw Error.fail t)
    (fun _ h _ => Necessity.compl_le h)
    (fun _ h _ => Necessity.le_compl h)
-- TODO review 37 end

/-- Run `p`; if it fails with error `e`, run `recover e`. If recovery also
fails, report `p`'s original error. -/
def withRecovery
  (recover : ε' → Parser ε ⟨ge, gc⟩ α)
  (p : Parser ε' ⟨ge', gc'⟩ α)
  -- TODO review 38 begin
  : Parser ε' ⟨ge ⊓ ge', ge'.ite gc gc'⟩ α :=
  p.onOutcome
    (fun t h f => recover f.error |>.run t |>.handle ((recover f.error).sound t)
      (fun _ _ => Outcome.throwFailure f)
      (fun _ r => Outcome.ofSuccess
  -- TODO review 38 end
        { r with witness := consumptionWitness.ite_right h r.witness }))
    -- TODO review 39 begin
    (fun _ h r => Outcome.ofSuccess
    -- TODO review 39 end
      { r with witness := consumptionWitness.ite_left h r.witness })
    -- TODO review 40 begin
    (fun t h f => Outcome.handle_sound ((recover f.error).sound t) _ _
      (fun h' _ => le_inf h' h)
      (fun h' _ => inf_le_left.trans h'))
    (fun _ h _ => inf_le_right.trans h)
    -- TODO review 40 end

end Parser
