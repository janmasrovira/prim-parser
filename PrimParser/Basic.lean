import PrimParser.NonEmptyList
import PrimParser.Input
import PrimParser.Necessity
import PrimParser.GradedMonad

open Buffer

/-!
# PrimParser

A parser combinator library with precise grades tracking error and consumption
behavior at the type level via `Necessity`.
-/

abbrev Error := String

class ParserError (ε : Type) where
  /-- Unexpected end of input. -/
  endOfInput : ε

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
  errors := never
  consumes := always

abbrev conditional : Grade where
  errors := possibly
  consumes := always

abbrev flexible : Grade where
  errors := never
  consumes := possibly

abbrev fallible : Grade where
  errors := possibly
  consumes := possibly

abbrev pure : Grade where
  errors := never
  consumes := never

abbrev lookahead : Grade where
  errors := possibly
  consumes := never

abbrev empty : Grade where
  errors := always
  consumes := never

@[simp] def max (a b : Grade) : Grade := ⟨a.errors ⊔ b.errors, a.consumes ⊔ b.consumes⟩

instance : Max Grade where
  max := max

instance : Monoid Grade where
  mul := max
  mul_assoc a b c := by cases a; cases b; cases c; simp [HMul.hMul, Mul.mul, sup_assoc]
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
  {gc gc' : Necessity}
  {ε : Type}

/-- Relates input size `n` and remaining size `m` according to a consumption grade:
`always` requires strict decrease, `possibly` allows `≤`, `never` requires equality. -/
abbrev consumptionWitness (n m : Nat) : Necessity → Prop
  | always => n < m
  | possibly => n ≤ m
  | never => n = m

@[simp] theorem consumptionWitness.rfl (h : gc ≤ possibly) : consumptionWitness n n gc := by
  cases gc <;> simp
  contradiction

theorem consumptionWitness.le : consumptionWitness n m gc → n ≤ m := by
  cases gc <;> omega

theorem consumptionWitness.inf_of_possibly_le {x : Necessity}
  (h : possibly ≤ x)
  (w : consumptionWitness n m gc)
  : consumptionWitness n m (x ⊓ gc) := by
  cases x <;> cases gc <;> first | contradiction | (simp_all <;> omega)

theorem consumptionWitness.trans {n1 n2 n3 : Nat}
  (w1 : consumptionWitness n2 n1 gc)
  (w2 : consumptionWitness n3 n2 gc')
  : consumptionWitness n3 n1 (gc ⊔ gc') := by
  cases gc <;> cases gc' <;> simp_all <;> omega

/-- A successful parse result. -/
structure Success (n : Nat) (consumes : Necessity) (α : Type) where
  result : α
  restSize : Nat
  witness : consumptionWitness restSize n consumes := by
    first | omega | simp

/-- A failed parse result -/
structure Failure (n : Nat) (ε : Type) where
  error : ε
  restSize : Nat
  witness : restSize ≤ n := by
    first | omega | simp

def Failure.trans (f : Failure m ε) (h : m ≤ n) : Failure n ε where
  error := f.error
  restSize := f.restSize
  witness := Nat.le_trans f.witness h

@[simp] theorem Failure.trans_rfl (f : Failure n ε) : f.trans (by simp) = f := by
  simp [trans]

/-- The result type of running a parser. -/
inductive Outcome (ε : Type) (n : Nat) (consumes : Necessity) (α : Type) : Type where
  | failure (f : Failure n ε)
  | success (r : Success n consumes α)

export Outcome (failure success)

abbrev Outcome.Sound (errors : Necessity) {c : Necessity} {α : Type} (o : Outcome ε n c α) : Prop :=
  match o with
  | failure _ => possibly ≤ errors
  | success _ => errors ≤ possibly

@[simp] theorem Outcome.sound_possibly {α} {o : Outcome ε n gc α} : Sound possibly o := by
  cases o <;> simp [Outcome.Sound]

end Parser

/-- A parser with error type `ε`, static grade `g`, and result type `α`.
The grade tracks error and consumption behavior at the type level. -/
structure Parser (σ τ : Type) [Buffer σ τ] (ε : Type) (g : Grade) (α : Type) where
  run : ∀ {n}, Input σ τ n → Parser.Outcome ε n g.consumes α
  sound : ∀ {n} (inp : Input σ τ n), Parser.Outcome.Sound g.errors (run inp) := by
    intro _ _
    first
      | assumption
      | exact Parser.Outcome.sound_possibly
      | simp [Parser.Outcome.Sound]

namespace Parser

abbrev TokenParser (τ ε : Type) (g : Grade) (α : Type) : Type := Parser (Array τ) τ ε g α

variable
  {σ τ : Type} [Buffer σ τ]
  {α β γ ε ε' : Type}
  {n m : Nat}
  {g g' : Grade}
  {ge ge' : Necessity} -- used for `errors`
  {gc gc' : Necessity} -- used for `consumes`

@[ext] theorem ext
  {p q : Parser σ τ ε g α}
  (h : ∀ {m} (t : Input σ τ m), p.run t = q.run t)
  : p = q := by
  obtain ⟨pr, ps⟩ := p; obtain ⟨qr, qs⟩ := q
  have hr : @pr = @qr := by funext m t; exact h t
  subst hr; rfl

@[inline] def Outcome.handle
  (o : Outcome ε n gc α)
  (sound : Sound ge o)
  (onSuccess : ge ≤ possibly → Success n gc α → β)
  (onError : possibly ≤ ge → Failure n ε → β)
  : β :=
  match o with
  | failure f => onError sound f
  | success r => onSuccess sound r

theorem Outcome.handle_prop
  {P : β → Prop}
  {o : Outcome ε n gc α}
  (sound : Sound ge o)
  {onSuccess : ge ≤ possibly → Success n gc α → β}
  {onError : possibly ≤ ge → Failure n ε → β}
  (hSuccess : ∀ h r, P (onSuccess h r))
  (hError : ∀ h f, P (onError h f))
  : P (o.handle sound onSuccess onError) :=
  match o with
  | failure f => hError sound f
  | success r => hSuccess sound r

theorem Outcome.handle_sound
  {o : Outcome ε n gc α}
  (sound : Sound ge o)
  {onSuccess : ge ≤ possibly → Success n gc α → Outcome ε' m gc' β}
  {onError : possibly ≤ ge → Failure n ε → Outcome ε' m gc' β}
  (soundSuccess : ∀ h r, Sound ge' (onSuccess h r))
  (soundError : ∀ h f, Sound ge' (onError h f))
  : Sound ge' (o.handle sound onSuccess onError) :=
  handle_prop sound soundSuccess soundError

namespace Outcome

variable
  {o : Outcome ε n gc α}
  {sound : Sound ge o}
  {onSuccess : ge ≤ possibly → Success n gc α → β}
  {onError : possibly ≤ ge → Failure n ε → β}

/-- Reduce `handle` when the outcome is known to succeed. -/
theorem handle_success
  {r : Success n gc α}
  (h : o = success r)
  (hge : ge ≤ possibly := by simp)
  : o.handle sound onSuccess onError = onSuccess hge r := by
  subst h; rfl

/-- Reduce `handle` when the outcome is known to fail. -/
theorem handle_failure
  {f : Failure n ε}
  (h : o = failure f)
  (hge : possibly ≤ ge := by simp)
  : o.handle sound onSuccess onError = onError hge f := by
  subst h; rfl

end Outcome

instance : Functor (Success n gc) where
  map f x := { x with result := f x.result }

instance : GradedFunctor (Success n) where
  gmap := Functor.map

instance : Functor (Outcome ε n gc) where
  map f o := match o with
    | failure e => failure e
    | success r => success (f <$> r)

theorem Outcome.map_sound (f : α → β) (o : Outcome ε n gc α) (ho : Sound ge o)
  : Sound ge (f <$> o) := by
  cases o <;> exact ho

def Error.eof : Error := "unexpected end of input"
def Error.fail : Error := "fail"

instance : ParserError Error where
  endOfInput := Error.eof

theorem Success.le (p : Success n gc α) : p.restSize ≤ n := consumptionWitness.le p.witness

def Success.weakenConsumes (p : Success n gc α) : Success n possibly α :=
  { p with witness := p.le }

def Success.trans (s : Success m gc α) (h : m ≤ n) : Success n (gc ⊔ possibly) α where
  result := s.result
  restSize := s.restSize
  witness := by
    have w := s.witness
    cases gc <;> simp_all <;> omega

@[simp] def Success.seq
  (r1 : Success n gc α)
  (r2 : Success r1.restSize gc' β)
  : Success n (gc ⊔ gc') β where
  result := r2.result
  restSize := r2.restSize
  witness := consumptionWitness.trans r1.witness r2.witness

@[inline, simp] def Success.bindParser {xc fe fc : Necessity}
  (t : Input σ τ n)
  (x : Success n xc α)
  (f : α → Parser σ τ ε ⟨fe, fc⟩ β)
  : Outcome ε n (xc ⊔ fc) β :=
  match f x.result |>.run (t.dropTo x.restSize x.le) with
  | failure e => failure (e.trans x.le)
  | success y => success (x.seq y)

instance : GradedFunctor (Parser σ τ ε) where
  gmap f p :=
    { run t := f <$> p.run t
      sound t := Outcome.map_sound f (p.run t) (p.sound t) }

def Outcome.throw (e : ε) : Outcome ε n gc α :=
  failure { error := e, restSize := n }

theorem Outcome.throw_sound {e : ε} (h : possibly ≤ ge)
  : Sound ge (Outcome.throw (α := α) (gc := gc) (n := n) e) := h

@[inline] def handle
  (p : Parser σ τ ε g α)
  (onSuccess : ∀ {n}, Input σ τ n →
    g.errors ≤ possibly → Success n g.consumes α → Outcome ε' n g'.consumes β)
  (soundSuccess : ∀ {n} {t : Input σ τ n} h r, Outcome.Sound g'.errors (onSuccess t h r))
  (onError : ∀ {n}, Input σ τ n →
    possibly ≤ g.errors → Failure n ε → Outcome ε' n g'.consumes β)
  (soundError : ∀ {n} {t : Input σ τ n} h f, Outcome.Sound g'.errors (onError t h f))
  : Parser σ τ ε' g' β where
  run t := p.run t |>.handle (p.sound t) (onSuccess t) (onError t)
  sound t := Outcome.handle_sound (p.sound t) (soundSuccess (t := t)) soundError

/-- Monadic bind for parsers. The resulting grade is the product (max)
of the two grades. -/
def bind
  (m : Parser σ τ ε g α)
  (f : α → Parser σ τ ε g' β)
  : Parser σ τ ε (g * g') β :=
  m.handle
    (onSuccess := fun t _ x => x.bindParser t f)
    (soundSuccess := fun {_} {t} h x => by
      have hsound := f x.result |>.sound (t.dropTo x.restSize x.le)
      cases hrun : f x.result |>.run (t.dropTo x.restSize x.le) with
      | failure e =>
        simp [Success.bindParser, hrun] at hsound ⊢
        exact le_sup_of_le_right hsound
      | success y =>
        simp [Success.bindParser, hrun] at hsound ⊢
        exact sup_le h hsound)
    (onError := fun _ _ e => failure e)
    (soundError := fun h _e => le_sup_of_le_left h)

instance [i : Nonempty σ] : IsEmpty (Parser σ τ ε impossible α) where
  false p := i.elim fun s => by
    let inp : Input σ τ 0 := ⟨s, Nat.zero_le _⟩
    have h := p.sound inp
    cases hr : p.run inp with
    | failure f => rw [hr] at h; contradiction
    | success s => have := s.witness; omega

/-- Lift a value into a parser that consumes nothing and never fails. -/
abbrev pure (a : α) : Parser σ τ ε 1 α where
  run {n} _ := success { result := a, restSize := n, witness := rfl }

instance : GradedApplicative (Parser σ τ ε) where
  gpure := pure
  gseq f g := bind f fun f' =>
    { run t := f' <$> (g ()).run t
      sound t := Outcome.map_sound f' ((g ()).run t) ((g ()).sound t) }

instance : GradedMonad (Parser σ τ ε) where
  gbind := bind

theorem gmap_run (f : α → β) (p : Parser σ τ ε g α) (t : Input σ τ n)
  : (f <$>ᵍ p).run t = f <$> p.run t := rfl

theorem gbind_run (m : Parser σ τ ε g α) (k : α → Parser σ τ ε g' β) (t : Input σ τ n)
  : (m >>=ᵍ k).run t
    = (m.run t).handle (m.sound t) (fun _ x => x.bindParser t k) (fun _ e => failure e) := rfl

private def fixGo [ParserError ε]
  {n : Nat}
  (h : possibly ≤ ge)
  (f : Parser σ τ ε ⟨ge, always⟩ α → Parser σ τ ε ⟨ge, always⟩ α)
  (t : Input σ τ n)
  : {o : Outcome ε n always α // Outcome.Sound ge o} :=
  let self : Parser σ τ ε ⟨ge, always⟩ α :=
    { run {k} t' :=
        if hk : k < n
        then fixGo h f t' |>.val
        else Outcome.throw ParserError.endOfInput
      sound {k} t' := by
        split
        · exact fixGo h f t' |>.property
        · exact Outcome.throw_sound h }
  { val := f self |>.run t
    property := f self |>.sound t }

/-- Build a recursive parser via a fixpoint. Termination is guaranteed by
requiring the body to always consume input. -/
def fix [ParserError ε]
  (f : Parser σ τ ε ⟨ge, always⟩ α → Parser σ τ ε ⟨ge, always⟩ α)
  (h : possibly ≤ ge := by simp)
  : Parser σ τ ε ⟨ge, always⟩ α where
  run t := fixGo h f t |>.val
  sound t := fixGo h f t |>.property

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

/-- Run `p`. If it fails, restores the original input. -/
def withBacktracking {g} (p : Parser σ τ ε g α) : Parser σ τ ε g α :=
  p.handle
    (onSuccess := fun _ _ s => success s)
    (soundSuccess := fun h _ => h)
    (onError := fun {n} _ _ f => failure { error := f.error, restSize := n })
    (soundError := fun h _ => h)

/-- Try `p1`; if it fails, run `p2`. -/
def choice
  (p1 : Parser σ τ ε ⟨ge, gc⟩ α)
  (p2 : Parser σ τ ε ⟨ge', gc'⟩ α)
  : Parser σ τ ε ⟨ge ⊓ ge', ge.ite gc' gc⟩ α :=
  p1.handle
    (onSuccess := fun _ hge s => success
      { s with witness := consumptionWitness.ite_left hge s.witness })
    (soundSuccess := fun hge _ => inf_le_left.trans hge)
    (onError := fun t hge _ =>
      p2.run t |>.handle (p2.sound t)
        (fun _ s' => success
          { s' with witness := consumptionWitness.ite_right hge s'.witness })
        (fun _ f' => failure f'))
    (soundError := fun {_} {t} hge _f => Outcome.handle_sound (p2.sound t)
      (soundError := fun hge' _ => le_inf hge hge')
      (soundSuccess := fun hge' _ => inf_le_right.trans hge'))

infixl:20 " <|> " => choice

/-- try `p1`; if it fails *without consuming*, then try `p2` -/
def committedChoice
  (p1 : Parser σ τ ε ⟨ge, gc⟩ α)
  (p2 : Parser σ τ ε ⟨ge', gc'⟩ α)
  : Parser σ τ ε ⟨ge ⊓ (ge' ⊔ possibly), ge.ite gc' gc⟩ α :=
  p1.handle
    (onSuccess := fun _ hge s => success
      { s with witness := consumptionWitness.ite_left hge s.witness })
    (soundSuccess := fun hge _ => inf_le_left.trans hge)
    (onError := fun {n} t hge f =>
      if f.restSize = n
      then
        p2.run t |>.handle (p2.sound t)
          (fun _ s' => success
            { s' with witness := consumptionWitness.ite_right hge s'.witness })
          (fun _ f' => failure f')
      else failure f)
    (soundError := fun {n} t hge f => by
      if c : f.restSize = n
      then
        simp [c]; apply Outcome.handle_sound
        case soundError => intro _ _; simpa [Outcome.Sound]
        case soundSuccess =>
          intro hge' _
          simp only [Outcome.Sound]
          simp at hge' ⊢; right; assumption
      else simp [c]; simpa [Outcome.Sound])

/-- Try `p1` first, if it fails with `Failure f`, run `p2` on the input left at `f.restSize` -/
def tryResume
  (p1 : Parser σ τ ε ⟨ge, gc⟩ α)
  (p2 : Parser σ τ ε ⟨ge', gc'⟩ α)
  : Parser σ τ ε ⟨ge ⊓ ge', ge.ite (gc' ⊔ possibly) gc⟩ α :=
  p1.handle
    (onSuccess := fun _ hge s => success
      { s with witness := consumptionWitness.ite_left hge s.witness })
    (soundSuccess := fun hge _ => inf_le_left.trans hge)
    (onError := fun t hge f =>
      let rest := t.dropTo f.restSize f.witness
      p2.run rest |>.handle (p2.sound rest)
        (fun _ s' =>
          let lifted := s'.trans f.witness
          success { lifted with witness := consumptionWitness.ite_right hge lifted.witness })
        (fun _ f' => failure (f'.trans f.witness)))
    (soundError := fun {_} {t} hge f =>
      Outcome.handle_sound (p2.sound (t.dropTo f.restSize f.witness))
      (soundError := fun hge' _ => le_inf hge hge')
      (soundSuccess := fun hge' _ => inf_le_right.trans hge'))

/-- Try each parser in the list in order, returning the first success. -/
def oneOf (l : NonEmptyList (Parser σ τ ε g α)) : Parser σ τ ε g α :=
  let rec go (l : List (Parser σ τ ε g α)) (p : l.length ≠ 0 := by simp)
      : Parser σ τ ε g α :=
    match l with
    | [] => nomatch p
    | [x] => x
    | x :: y :: xs => by
      refine cast ?_ (choice x (go (y :: xs)))
      congr 2 <;> simp
  go l.1 (p := by simpa using l.2)

/-- A parser that always fails with error `e`. -/
def throw (e : ε) (c : possibly ≤ ge := by simp) : Parser σ τ ε ⟨ge, gc⟩ α where
  run _ := Outcome.throw e

def Success.relaxConsumes (p : Success n gc α) : Success n (gc ⊓ possibly) α :=
  match gc with
  | never | possibly => p
  | always => { p with witness := le_of_lt p.witness }

/-- Weaken the consumption grade by capping at `possibly`. -/
def relaxConsumes (p : Parser σ τ ε ⟨ge, gc⟩ α) : Parser σ τ ε ⟨ge, gc ⊓ possibly⟩ α :=
  p.handle
    (onSuccess := fun _ _ r => success r.relaxConsumes)
    (soundSuccess := fun h _ => h)
    (onError := fun _ _ f => failure f)
    (soundError := fun h _ => h)

/-- Weaken the error grade by capping at `possibly`. -/
def relaxErrors (p : Parser σ τ ε ⟨ge, gc⟩ α) : Parser σ τ ε ⟨ge ⊓ possibly, gc⟩ α :=
  p.handle
    (onSuccess := fun _ _ r => success r)
    (soundSuccess := fun _ _ => inf_le_right)
    (onError := fun _ _ f => failure f)
    (soundError := fun h _ => le_inf h le_rfl)

/-- Cap both error and consumption grades at `possibly`. -/
def relax (p : Parser σ τ ε ⟨ge, gc⟩ α) : Parser σ τ ε ⟨ge ⊓ possibly, gc ⊓ possibly⟩ α :=
  p.relaxErrors.relaxConsumes

/-- Forget consumption precision, setting it to `possibly`. -/
def weakenConsumes (p : Parser σ τ ε ⟨ge, gc⟩ α) : Parser σ τ ε ⟨ge, possibly⟩ α :=
  p.handle
    (onSuccess := fun _ _ r => success r.weakenConsumes)
    (soundSuccess := fun h _ => h)
    (onError := fun _ _ f => failure f)
    (soundError := fun h _ => h)

/-- Forget error precision, setting it to `possibly`. -/
def weakenErrors (p : Parser σ τ ε ⟨ge, gc⟩ α) : Parser σ τ ε ⟨possibly, gc⟩ α :=
  p.handle
    (onSuccess := fun _ _ r => success r)
    (soundSuccess := fun _ _ => le_rfl)
    (onError := fun _ _ f => failure f)
    (soundError := fun _ _ => le_rfl)

/-- Weaken both grades to `possibly`, yielding a `fallible` parser. -/
def weaken (p : Parser σ τ ε ⟨ge, gc⟩ α) : Parser σ τ ε fallible α :=
  p.weakenErrors.weakenConsumes

/-- Run a parser on a `Input`. -/
def runOn (p : Parser σ τ ε g α) (t : Input σ τ n) : Except ε α :=
  (p.run t).handle (p.sound t) (fun _ r => .ok r.result) (fun _ f => .error f.error)

abbrev Except.Sound (errors : Necessity) {α : Type} (r : Except ε α) : Prop :=
  match r with
  | .error _ => possibly ≤ errors
  | .ok _ => errors ≤ possibly

theorem runOn_sound (p : Parser σ τ ε g α) (t : Input σ τ n)
  : Except.Sound g.errors (p.runOn t) :=
  Outcome.handle_prop (p.sound _) (fun h _ => h) (fun h _ => h)

/-- Consume a single token. -/
def anyTok : Parser σ τ Error conditional τ where
  run {n} inp :=
    match h : inp.nextTok with
    | some t =>
      have hle := inp.width_le h
      have hpos := Buffer.width_pos (σ := σ) t
      success { result := t
                restSize := n - width σ t }
    | none => failure { error := Error.eof, restSize := n }

section

variable {t : τ} {inp : Input σ τ n}

theorem anyTok_run_some
  (h : inp.nextTok = some t := by assumption)
  : anyTok.run inp
    = success { result := t
                restSize := n - width σ t
                witness := Input.sub_width_lt h } := by
  simp only [anyTok]; split <;> rw [h] at * <;> simp_all

theorem anyTok_run_eof
  (h : inp.nextTok = none := by
    first | assumption | exact Input.nextTok_eq_none)
  : anyTok.run inp
    = failure { error := Error.eof
                restSize := n } := by
  simp only [anyTok]; split <;> simp_all

end

/-- Like `gpure` but with a flexible grade: both `ge` and `gc` can be `never`
or `possibly`. Useful in match branches where all cases must share the same grade. -/
def ok (a : α) (he : ge ≤ possibly := by simp) (hc : gc ≤ possibly := by simp)
  : Parser σ τ ε ⟨ge, gc⟩ α where
  run {n} _ := success { result := a, restSize := n, witness := consumptionWitness.rfl hc }

/-- Consume a token and apply `f`; succeed with the result or fail if `f` returns `none`. -/
def token (f : τ → Option α) : Parser σ τ Error conditional α := gdo
  let t ← anyTok
  (match f t with
   | .some r => ok (gc := never) r
   | .none => throw (ge := possibly) Error.fail)

/-- Consume a token that satisfies predicate `f`, or fail. -/
def satisfy (f : τ → Bool) : Parser σ τ Error conditional τ :=
  token (fun t => if f t then .some t else .none)

section

variable {f : τ → Bool} {t : τ} {inp : Input σ τ n}

theorem satisfy_run_accept
  (h : inp.nextTok = some t := by assumption)
  (cond : f t = true := by assumption)
  : (satisfy f).run inp
    = success { result := t
                restSize := n - width σ t
                witness := Input.sub_width_lt h } := by
  rw [satisfy, token, gbind_run, Outcome.handle_success anyTok_run_some]
  simp [ok, cond]

theorem satisfy_run_reject
  (h : inp.nextTok = some t := by assumption)
  (hf : ¬ f t := by assumption)
  : (satisfy f).run inp
    = failure { error := Error.fail
                restSize := n - width σ t } := by
  have : consumptionWitness (n - width σ t) n always := by
    have := inp.width_le h
    have := Buffer.width_pos (σ := σ) t
    omega
  simp [satisfy, token, gbind_run]
  rw [Outcome.handle_success anyTok_run_some]
  simp [throw, Outcome.throw, hf, Failure.trans]

theorem satisfy_run_eof
  (h : inp.nextTok = none := by
    first | assumption | exact Input.nextTok_eq_none)
  : (satisfy f).run inp
    = failure { error := Error.eof
                restSize := n } := by
  simp only [satisfy, token, gbind_run]
  rw [Outcome.handle_failure anyTok_run_eof]

end

/-- Like `satisfy` but returns `PUnit`. -/
def skipSatisfy (f : τ → Bool) : Parser σ τ Error conditional PUnit :=
  () <$ᵍ satisfy f

/-- Try `p`; return `some result` on success or `none` on failure, never failing itself. -/
def optional (p : Parser σ τ ε ⟨ge, gc⟩ α) : Parser σ τ ε ⟨never, ge.complement ⊓ gc⟩ (Option α) where
  run {n} t := success <| match p.run t, p.sound t with
    | failure _, hs =>
      { result := .none
        restSize := n
        witness := consumptionWitness.rfl (inf_le_left.trans (Necessity.compl_le hs)) }
    | success r, hs =>
      { result := .some r.result
        restSize := r.restSize
        witness := consumptionWitness.inf_of_possibly_le (Necessity.le_compl hs) r.witness }

/-- Try `p`; return the result on success or the default value `d` on failure. -/
def optionalD (p : Parser σ τ ε ⟨ge, gc⟩ α) (d : α) : Parser σ τ ε ⟨never, ge.complement ⊓ gc⟩ α :=
  (·.getD d) <$>ᵍ optional p

/-- Try `p`, discarding the result; never fails. -/
def skipOptional (p : Parser σ τ ε ⟨ge, gc⟩ α) : Parser σ τ ε ⟨never, ge.complement ⊓ gc⟩ PUnit :=
  () <$ᵍ optional p

/-- Try `p`; report whether it succeeded, never failing itself. -/
def test (p : Parser σ τ ε ⟨ge, gc⟩ α) : Parser σ τ ε ⟨never, ge.complement ⊓ gc⟩ Bool :=
  Option.isSome <$>ᵍ optional p

/-- Repeatedly apply `p` until `e` succeeds, collecting the results of `p`. -/
def manyTill [ParserError ε]
  (p : Parser σ τ ε ⟨ge, always⟩ α)
  (e : Parser σ τ ε ⟨ge', always⟩ β)
  : Parser σ τ ε ⟨ge, always⟩ (List α) :=
  match ge with
  | always | never => (fun x => [x]) <$>ᵍ p
  | possibly =>
      fix fun self =>
        oneOf (
          ([] <$ᵍ e |>.weakenErrors) ::₁
          [gdo let a ← p; let as ← self; return (a :: as)]
        )

/-- Apply `p` zero or more times, collecting results. Requires `p` to always consume. -/
def many (p : Parser σ τ ε ⟨ge, always⟩ α) : Parser σ τ ε flexible (List α) where
  run :=
    let rec go {n} (t : Input σ τ n) : Success n possibly (List α) :=
      match p.run t with
      | .failure _ => { result := [], restSize := n }
      | .success r =>
        have : r.restSize < n := r.witness
        let rest := go (t.dropTo r.restSize r.le)
        { result := r.result :: rest.result
          restSize := rest.restSize
          witness := by have := rest.witness; omega }
    fun t => success (go t)

/-- Apply `p` one or more times, collecting results. -/
def many1 (p : Parser σ τ ε ⟨ge, always⟩ α) : Parser σ τ ε ⟨ge, always⟩ (NonEmptyList α) := gdo
  let x ← p
  let xs ← many p
  return x ::₁ xs
  grade_by by simp

/-- Apply `p` zero or more times, discarding results. -/
def skipMany (p : Parser σ τ ε ⟨ge, always⟩ α) : Parser σ τ ε flexible PUnit :=
  () <$ᵍ many p

/-- Apply `p` one or more times, discarding results. -/
def skipMany1 (p : Parser σ τ ε ⟨ge, always⟩ α) : Parser σ τ ε ⟨ge, always⟩ PUnit :=
  () <$ᵍ many1 p

/-- Parse `p` surrounded by the delimiters `l` and `r`. -/
def rawBracket (l r : Parser σ τ Error conditional PUnit) (p : Parser σ τ Error ⟨ge, gc⟩ α)
  : Parser σ τ Error ⟨ge ⊔ possibly, always⟩ α := gdo
  l
  let x ← p
  r
  return x
  grade_by by simp

/-- Parse `sep` then `p`, returning `p`'s result; always consumes. -/
private def sepItem
  (sep : Parser σ τ ε ⟨ge', gc'⟩ β)
  (p : Parser σ τ ε ⟨ge, gc⟩ α)
  (h : gc' ⊔ gc = always := by simp)
  : Parser σ τ ε ⟨ge' ⊔ ge, always⟩ α := gdo
  let _ ← sep; p
  grade_by by simp [h]

/-- Parse zero or more occurrences of `p` separated by `sep`. -/
def sepBy
  (sep : Parser σ τ ε ⟨ge', gc'⟩ β)
  (p : Parser σ τ ε ⟨ge, gc⟩ α)
  (h : gc' ⊔ gc = always := by simp)
  : Parser σ τ ε flexible (List α) := weakenConsumes <| gdo
  let m ← optional p
  (match m with
   | .some f => gdo
     let rest ← many (sepItem sep p h)
     ok (gc := possibly) (f :: rest)
   | .none => ok (ge := never) [])
  grade_by by rfl

/-- Parse one or more occurrences of `p` separated by `sep`. -/
def sepBy1
  (sep : Parser σ τ ε ⟨ge', gc'⟩ β)
  (p : Parser σ τ ε ⟨ge, gc⟩ α)
  (h : gc' ⊔ gc = always := by simp)
  : Parser σ τ ε ⟨ge, gc ⊔ possibly⟩ (NonEmptyList α) := gdo
  let first ← p
  let rest ← many (sepItem sep p h)
  return first ::₁ rest
  grade_by by simp

/-- Parse `p` then `sep`, returning `p`'s result; always consumes. -/
private def endItem
  (sep : Parser σ τ ε ⟨ge', gc'⟩ β)
  (p : Parser σ τ ε ⟨ge, gc⟩ α)
  (h : gc ⊔ gc' = always := by simp)
  : Parser σ τ ε ⟨ge ⊔ ge', always⟩ α := gdo
  let x ← p; let _ ← sep; return x
  grade_by by simp [h]

/-- Parse zero or more occurrences of `p`, each followed by `sep`. -/
def endBy
  (sep : Parser σ τ ε ⟨ge', gc'⟩ β)
  (p : Parser σ τ ε ⟨ge, gc⟩ α)
  (h : gc ⊔ gc' = always := by simp)
  : Parser σ τ ε flexible (List α) :=
  many (endItem sep p h)

/-- Parse one or more occurrences of `p`, each followed by `sep`. -/
def endBy1
  (sep : Parser σ τ ε ⟨ge', gc'⟩ β)
  (p : Parser σ τ ε ⟨ge, gc⟩ α)
  (h : gc ⊔ gc' = always := by simp)
  : Parser σ τ ε ⟨ge ⊔ ge', always⟩ (NonEmptyList α) :=
  many1 (endItem sep p h)

/-- Parse one or more occurrences of `p` separated by `sep`, with an optional
trailing `sep`. -/
def sepEndBy1
  (sep : Parser σ τ ε ⟨ge', gc'⟩ β)
  (p : Parser σ τ ε ⟨ge, gc⟩ α)
  (h : gc' ⊔ gc = always := by simp)
  : Parser σ τ ε ⟨ge, gc ⊔ possibly⟩ (NonEmptyList α) := gdo
  let xs ← sepBy1 sep p (h := h)
  weakenConsumes (skipOptional sep)
  return xs
  grade_by by simp

/-- Parse zero or more occurrences of `p` separated by `sep`, with an optional
trailing `sep`. -/
def sepEndBy
  (sep : Parser σ τ ε ⟨ge', gc'⟩ β)
  (p : Parser σ τ ε ⟨ge, gc⟩ α)
  (h : gc' ⊔ gc = always := by simp)
  : Parser σ τ ε flexible (List α) := gdo
  let xs ← sepBy sep p (h := h)
  weakenConsumes (skipOptional sep)
  return xs

/-- Parse exactly `n + 1` occurrences of `p`. -/
def count1
  (n : Nat)
  (p : Parser σ τ ε ⟨ge, gc⟩ α)
  : Parser σ τ ε ⟨ge, gc⟩ (List.Vector α (n + 1)) :=
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
  (p : Parser σ τ ε ⟨ge, gc⟩ α)
  : Parser σ τ ε ⟨ge ⊓ possibly, gc ⊓ possibly⟩ (List.Vector α n) :=
  match n with
  | 0 => ok .nil
  | n + 1 => count1 n p |>.relax

/-- Skip exactly `n` occurrences of `p`. -/
def skip (n : Nat) (p : Parser σ τ ε ⟨ge, gc⟩ α)
  : Parser σ τ ε ⟨ge ⊓ possibly, gc ⊓ possibly⟩ PUnit :=
  () <$ᵍ count n p

/-- Skip up to `n` occurrences of `p`. -/
def skipUpTo : (n : Nat) → Parser σ τ ε ⟨ge, always⟩ α → Parser σ τ ε flexible PUnit
  | 0, _ => ok ()
  | n + 1, p => gdo
    let m ← weakenConsumes (optional p)
    (match m with
     | .none => ok (ge := never) ()
     | .some _ => skipUpTo n p)

/-- Skip `n` or more occurrences of `p`. -/
def skipManyN (n : Nat) (p : Parser σ τ ε ⟨ge, always⟩ α)
  : Parser σ τ ε ⟨ge ⊓ possibly, possibly⟩ PUnit := gdo
  skip n p
  skipMany p
  grade_by by simp

/-- Run `p` until `stop` succeeds; discard `p`'s results. -/
def skipUntil [ParserError ε]
  (stop : Parser σ τ ε ⟨ge', always⟩ β)
  (p : Parser σ τ ε ⟨ge, always⟩ α)
  : Parser σ τ ε ⟨ge, always⟩ PUnit :=
  () <$ᵍ manyTill p stop

/-- Parse exactly `n` occurrences of `p` separated by `sep`. -/
def sepByN
  (sep : Parser σ τ ε ⟨ge', gc'⟩ β)
  (p : Parser σ τ ε ⟨ge, gc⟩ α)
  : (n : Nat) → Parser σ τ ε fallible (List.Vector α n)
  | 0 => ok .nil
  | n + 1 => (gdo
    let sepP := gdo
      let _ ← sep; p
    let p1 ← p
    let ps ← count n sepP
    return (p1 ::ᵥ ps)) |>.weaken

/-- Parse one or more occurrences of `p` separated by left-associative operator `op`. -/
def chainl1
  (op : Parser σ τ ε ⟨ge', always⟩ (α → α → α))
  (p : Parser σ τ ε ⟨ge, always⟩ α)
  : Parser σ τ ε ⟨ge, always⟩ α := gdo
  let x ← p
  let rest ← many (gdo
    let f ← op
    let y ← p
    return (f, y))
  return rest.foldl (fun acc ⟨f, y⟩ => f acc y) x
  grade_by by simp

/-- Succeed only at end of input, consuming nothing. -/
def eof : Parser σ τ Error lookahead PUnit where
  run {n} t := match n with
    | .zero => ok () |>.run t
    | _ => throw Error.fail |>.run t

/-- Run `p` without consuming input, keeping only the result. -/
def lookahead (p : Parser σ τ Error ⟨ge, gc⟩ α) : Parser σ τ Error ⟨ge, never⟩ α :=
  p.handle
    (onSuccess := fun {n} _ h r => success { result := r.result, restSize := n })
    (soundSuccess := fun h _ => h)
    (onError := fun _ h f => failure f)
    (soundError := fun h _ => h)

def peek : Parser σ τ Error Grade.lookahead τ := lookahead anyTok

/-- Succeed (without consuming) only when `p` fails. -/
def notFollowedBy (p : Parser σ τ Error ⟨ge, gc⟩ α) : Parser σ τ Error ⟨ge.complement, never⟩ PUnit :=
  p.handle
    (onSuccess := fun _ h _ => Outcome.throw Error.fail)
    (soundSuccess := fun h _ => Necessity.le_compl h)
    (onError := fun {n} _ h _ => success { result := (), restSize := n })
    (soundError := fun h _ => Necessity.compl_le h)

/-- Run `p`; if it fails with error `e`, run `recover e`. If recovery also
fails, report `p`'s original error. -/
def withRecovery
  (recover : ε' → Parser σ τ ε ⟨ge, gc⟩ α)
  (p : Parser σ τ ε' ⟨ge', gc'⟩ α)
  : Parser σ τ ε' ⟨ge ⊓ ge', ge'.ite gc gc'⟩ α :=
  p.handle
    (onSuccess := fun _ h r => success
      { r with witness := consumptionWitness.ite_left h r.witness })
    (soundSuccess := fun h _ => inf_le_right.trans h)
    (onError := fun t h f => recover f.error |>.run t |>.handle (recover f.error |>.sound t)
      (onError := fun _ _ => failure f)
      (onSuccess := fun _ r => success
        { r with witness := consumptionWitness.ite_right h r.witness }))
    (soundError := fun {_} {t} h f => Outcome.handle_sound ((recover f.error).sound t)
      (soundError := fun h' _ => le_inf h' h)
      (soundSuccess := fun h' _ => inf_le_left.trans h'))

end Parser
