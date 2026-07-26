import PrimParser.NonEmptyList
import PrimParser.Necessity
import PrimParser.GradedMonad

/-!
# PrimParser

A parser combinator library with precise grades tracking error and consumption
behavior at the type level via `Necessity`.
-/

abbrev Error := String

/-- Input to a parser. `n` is the number of bytes that haven't been consumed yet. -/
structure Text (n : Nat) where
  bytes : ByteArray
  valid : n ≤ bytes.size

@[inline] def Text.pos {n : Nat} (t : Text n) : Nat := t.bytes.size - n

theorem Text.pos_lt {n : Nat} (t : Text (n + 1)) : t.pos < t.bytes.size := by
  have := t.valid; simp only [Text.pos]; omega

@[inline] def Text.head {n : Nat} (t : Text (n + 1)) : UInt8 :=
  have := t.pos_lt
  t.bytes[t.pos]

theorem Text.utf8Size_le
  {n : Nat} {c : Char}
  (t : Text n)
  (h : t.bytes.utf8DecodeChar? t.pos = some c)
  : c.utf8Size ≤ n := by
  have hle := ByteArray.le_size_of_utf8DecodeChar?_eq_some h
  have hv := t.valid
  simp only [Text.pos] at hle
  omega

def Text.ofString (s : String) : Text s.toUTF8.size where
  bytes := s.toUTF8
  valid := by simp

def Text.empty : Text 0 := { bytes := .empty, valid := by simp }

@[inline] def Text.dropTo {n : Nat} (t : Text n) (m : Nat) (h : m ≤ n) : Text m where
  bytes := t.bytes
  valid := h.trans t.valid

@[simp] theorem Text.dropTo_self {n : Nat} (t : Text n) (h : n ≤ n) : t.dropTo n h = t := rfl

@[simp] theorem Text.dropTo_trans {n m k : Nat} (t : Text n) (h : m ≤ n) (h' : k ≤ m)
  : (t.dropTo m h).dropTo k h' = t.dropTo k (h'.trans h) := rfl

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
  cases a <;> omega

theorem consumptionWitness.inf_of_possibly_le {x : Necessity} (h : possibly ≤ x)
    (w : consumptionWitness n m gc) : consumptionWitness n m (x ⊓ gc) := by
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
  witness : consumptionWitness restSize n consumes := by simp

/-- A failed parse result -/
structure Failure (n : Nat) (ε : Type) where
  error : ε
  restSize : Nat
  witness : restSize ≤ n := by simp

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

@[simp] theorem Outcome.sound_possibly {α} (o : Outcome ε n gc α) : Sound possibly o := by
  cases o <;> simp [Outcome.Sound]

end Parser

/-- A parser with error type `ε`, static grade `g`, and result type `α`.
The grade tracks error and consumption behavior at the type level. -/
structure Parser (ε : Type) (g : Grade) (α : Type) where
  run : ∀ {n}, Text n → Parser.Outcome ε n g.consumes α
  sound : ∀ {n} (t : Text n), Parser.Outcome.Sound g.errors (run t)

namespace Parser

variable
  {α β γ ε ε' : Type}
  {n m : Nat}
  {g g' : Grade}
  {ge ge' : Necessity} -- used for `errors`
  {gc gc': Necessity} -- used for `consumes`

@[inline] def Outcome.handle
  (o : Outcome ε n gc α)
  (sound : Sound ge o)
  (onSuccess : ge ≤ possibly → Success n gc α → β)
  (onError : possibly ≤ ge → Failure n ε → β)
  : β :=
  match o with
  | failure f => onError sound f
  | success r => onSuccess sound r

theorem Outcome.handle_sound
  {o : Outcome ε n gc α}
  (sound : Sound ge o)
  {onSuccess : ge ≤ possibly → Success n gc α → Outcome ε' m gc' β}
  {onError : possibly ≤ ge → Failure n ε → Outcome ε' m gc' β}
  (soundSuccess : ∀ h r, Sound ge' (onSuccess h r))
  (soundError : ∀ h f, Sound ge' (onError h f))
  : Sound ge' (o.handle sound onSuccess onError) :=
  match o with
  | failure f => soundError sound f
  | success r => soundSuccess sound r

instance : Functor (Success n gc) where
  map f x := {x with result := f x.result}

instance : GradedFunctor (Success n) where
  gmap := Functor.map

instance : Functor (Outcome ε n gc) where
  map f o := match o with
    | failure e => failure e
    | success r => success (f <$> r)

theorem Outcome.map_sound (f : α → β) (o : Outcome ε n gc α) (ho : Sound ge o)
  : Sound ge (f <$> o) := by
  cases o <;> exact ho

def Error.eof : Error := "eof"
def Error.fail : Error := "fail"

theorem Success.le (p : Success n gc α) : p.restSize ≤ n := consumptionWitness.le p.witness

def Success.weakenConsumes (p : Success n gc α) : Success n possibly α :=
  { p with witness := p.le }

def Success.trans (s : Success m gc α) (h : m ≤ n) : Success n (gc ⊔ possibly) α where
  result := s.result
  restSize := s.restSize
  witness := by
    have w := s.witness
    cases gc <;> simp_all <;> omega

def Success.seq
  (r1 : Success n gc α)
  (r2 : Success r1.restSize gc' β)
  : Success n (gc ⊔ gc') β where
  result := r2.result
  restSize := r2.restSize
  witness := consumptionWitness.trans r1.witness r2.witness

@[inline] def Success.bindParser {xc fe fc : Necessity}
  (t : Text n)
  (x : Success n xc α)
  (f : α → Parser ε ⟨fe, fc⟩ β)
  : Outcome ε n (xc ⊔ fc) β :=
  match f x.result |>.run (t.dropTo x.restSize x.le) with
  | failure e => failure (e.trans x.le)
  | success y => success (x.seq y)

instance : GradedFunctor (Parser ε) where
  gmap f p := {
    run t := f <$> p.run t
    sound t := Outcome.map_sound f (p.run t) (p.sound t)
  }

def Outcome.throw (e : ε) : Outcome ε n gc α :=
  failure { error := e, restSize := n }

theorem Outcome.throw_sound {e : ε} (h : possibly ≤ ge)
  : Sound ge (Outcome.throw (α := α) (gc := gc) (n := n) e) := h

@[inline] def handle
  (p : Parser ε g α)
  (onSuccess : ∀ {n}, Text n → g.errors ≤ possibly → Success n g.consumes α → Outcome ε' n g'.consumes β)
  (soundSuccess : ∀ {n} {t : Text n} h r, Outcome.Sound g'.errors (onSuccess t h r))
  (onError : ∀ {n}, Text n → possibly ≤ g.errors → Failure n ε → Outcome ε' n g'.consumes β)
  (soundError : ∀ {n} {t : Text n} h f, Outcome.Sound g'.errors (onError t h f))
  : Parser ε' g' β where
  run t := p.run t |>.handle (p.sound t) (onSuccess t) (onError t)
  sound t := Outcome.handle_sound (p.sound t) (soundSuccess (t := t)) soundError

/-- Monadic bind for parsers. The resulting grade is the product (max)
of the two grades. -/
def bind
  (m : Parser ε g α)
  (f : α → Parser ε g' β)
  : Parser ε (g * g') β :=
  m.handle
    (onSuccess := fun t _ x => x.bindParser t f)
    (soundSuccess := fun {_} {t} h x => by
      have hsound := f x.result |>.sound (t.dropTo x.restSize x.le)
      cases hrun : f x.result |>.run (t.dropTo x.restSize x.le) with
      | failure e => simp [Success.bindParser, hrun] at hsound ⊢
                     exact le_sup_of_le_right hsound
      | success y => simp [Success.bindParser, hrun] at hsound ⊢
                     exact sup_le h hsound)
    (onError := fun _ _ e => failure e)
    (soundError := fun h _e => le_sup_of_le_left h)

instance : IsEmpty (Parser ε impossible α) where
  false p := by
    have h := p.sound Text.empty
    cases hr : p.run Text.empty with
    | failure f => rw [hr] at h; contradiction
    | success s => have := s.witness; omega

/-- Lift a value into a parser that consumes nothing and never fails. -/
abbrev pure (a : α) : Parser ε 1 α where
  run {n} _ := success { result := a, restSize := n, witness := rfl }
  sound _ := by simp

instance : GradedApplicative (Parser ε) where
  gpure := pure
  gseq f g := bind f fun f' =>
    { run := fun t => f' <$> (g ()).run t
      sound := fun t => Outcome.map_sound f' ((g ()).run t) ((g ()).sound t) }

instance : GradedMonad (Parser ε) where
  gbind := bind

-- `Inhabited ε` is needed to throw a `default` error on empty input
private def fixGo [Inhabited ε]
    {n : Nat}
    (h : possibly ≤ ge)
    (f : Parser ε ⟨ge, always⟩ α → Parser ε ⟨ge, always⟩ α)
    (t : Text n)
    : {o : Outcome ε n always α // Outcome.Sound ge o} :=
  match n, t with
  | 0, _ => ⟨Outcome.throw default, Outcome.throw_sound h⟩
  | m + 1, t =>
    let self : Parser ε ⟨ge, always⟩ α :=
      { run := fun {k} t' =>
          if hk : k ≤ m then fixGo h f t' |>.val
          else Outcome.throw default
        sound := fun {k} t' => by
          split
          · exact fixGo h f t' |>.property
          · exact Outcome.throw_sound h }
    ⟨f self |>.run t, f self |>.sound t⟩

/-- Build a recursive parser via a fixpoint. Termination is guaranteed by
requiring the body to always consume input. -/
def fix [Inhabited ε]
  (f : Parser ε ⟨ge, always⟩ α → Parser ε ⟨ge, always⟩ α)
  (h : possibly ≤ ge := by simp)
  : Parser ε ⟨ge, always⟩ α :=
  { run := fun t => fixGo h f t |>.val
    sound := fun t => fixGo h f t |>.property }

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
  p.handle
    (onSuccess := fun _ _ s => success s)
    (soundSuccess := fun h _ => h)
    (onError := fun {n} _ _ f => failure { error := f.error, restSize := n })
    (soundError := fun h _ => h)

/-- Try `p1`; if it fails, run `p2`. -/
def choice
  (p1 : Parser ε ⟨ge, gc⟩ α)
  (p2 : Parser ε ⟨ge', gc'⟩ α)
  : Parser ε ⟨ge ⊓ ge', ge.ite gc' gc⟩ α :=
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
  (p1 : Parser ε ⟨ge, gc⟩ α)
  (p2 : Parser ε ⟨ge', gc'⟩ α)
  : Parser ε ⟨ge ⊓ (ge' ⊔ possibly), ge.ite gc' gc⟩ α :=
  p1.handle
    (onSuccess := fun _ hge s => success
      { s with witness := consumptionWitness.ite_left hge s.witness })
    (soundSuccess := fun hge _ => inf_le_left.trans hge)
    (onError := fun {n} t hge f =>
      if f.restSize = n then
        p2.run t |>.handle (p2.sound t)
          (fun _ s' => success
            { s' with witness := consumptionWitness.ite_right hge s'.witness })
          (fun _ f' => failure f')
      else
        failure f)
    (soundError := fun {n} t hge f => by
      if c : f.restSize = n
      then
        simp [c]; apply Outcome.handle_sound
        case soundError => intro _ _; simpa [Outcome.Sound]
        case soundSuccess => intro hge' _; simp only [Outcome.Sound]
                             simp at hge' ⊢; right; assumption
      else simp [c]; simpa [Outcome.Sound])

/-- Try `p1` first, if it fails with `Failure f`, run `p2` on the input left at `f.restSize` -/
def tryResume
  (p1 : Parser ε ⟨ge, gc⟩ α)
  (p2 : Parser ε ⟨ge', gc'⟩ α)
  : Parser ε ⟨ge ⊓ ge', ge.ite (gc' ⊔ possibly) gc⟩ α :=
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
def oneOf (l : NonEmptyList (Parser ε g α)) : Parser ε g α :=
  let rec go (l : List (Parser ε g α)) (p : l.length ≠ 0 := by simp) : Parser ε g α := match l with
      | [] => nomatch p
      | [x] => x
      | x :: y :: xs => by refine cast ?_ (choice x (go (y :: xs)))
                           congr 2 <;> simp
  go l.1 (p := by simpa using l.2)

/-- A parser that always fails with error `e`. -/
def throw (e : ε) (c : possibly ≤ ge := by simp) : Parser ε ⟨ge, gc⟩ α where
  run _ := Outcome.throw e
  sound _t := Outcome.throw_sound c

def Success.relaxConsumes (p : Success n gc α) : Success n (gc ⊓ possibly) α :=
  match gc with
  | never | possibly => p
  | always => { p with witness := le_of_lt p.witness }

/-- Weaken the consumption grade by capping at `possibly`. -/
def relaxConsumes (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge, gc ⊓ possibly⟩ α :=
  p.handle
    (onSuccess := fun _ _ r => success r.relaxConsumes)
    (soundSuccess := fun h _ => h)
    (onError := fun _ _ f => failure f)
    (soundError := fun h _ => h)

/-- Weaken the error grade by capping at `possibly`. -/
def relaxErrors (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge ⊓ possibly, gc⟩ α :=
  p.handle
    (onSuccess := fun _ _ r => success r)
    (soundSuccess := fun _ _ => inf_le_right)
    (onError := fun _ _ f => failure f)
    (soundError := fun h _ => le_inf h le_rfl)

/-- Cap both error and consumption grades at `possibly`. -/
def relax (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge ⊓ possibly, gc ⊓ possibly⟩ α :=
  p.relaxErrors.relaxConsumes

/-- Forget consumption precision, setting it to `possibly`. -/
def weakenConsumes (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge, possibly⟩ α :=
  p.handle
    (onSuccess := fun _ _ r => success r.weakenConsumes)
    (soundSuccess := fun h _ => h)
    (onError := fun _ _ f => failure f)
    (soundError := fun h _ => h)

/-- Forget error precision, setting it to `possibly`. -/
def weakenErrors (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨possibly, gc⟩ α :=
  p.handle
    (onSuccess := fun _ _ r => success r)
    (soundSuccess := fun _ _ => le_rfl)
    (onError := fun _ _ f => failure f)
    (soundError := fun _ _ => le_rfl)

/-- Weaken both grades to `possibly`, yielding a `fallible` parser. -/
def weaken (p : Parser ε ⟨ge, gc⟩ α) : Parser ε fallible α :=
  p.weakenErrors.weakenConsumes

/-- Run a parser, discarding the error and returning the `Success` as an `Option`. -/
def runOption (p : Parser ε ⟨ge, gc⟩ α) (t : Text n) : Option (Success n gc α) :=
  p.run t |>.handle (p.sound t) (fun _ r => .some r) (fun _ _ => .none)

/-- Run a parser, returning only the parsed value as an `Option`. -/
def runResult? (p : Parser ε ⟨ge, gc⟩ α) (t : Text n) : Option α :=
  (p.runOption t).map (·.result)

/-- Consume a single byte. -/
def anyByte : Parser Error conditional UInt8 where
  run {n} t := match n, t with
    | 0, _ => failure {error := Error.eof, restSize := 0}
    | m + 1, t => success {result := t.head, restSize := m}
  sound t := by simp

/-- Consume a single UTF-8 character. -/
def anyChar : Parser Error conditional Char where
  run {n} t :=
    match h : t.bytes.utf8DecodeChar? t.pos with
    | some c =>
      have hle := t.utf8Size_le h
      have hpos := Char.utf8Size_pos c
      success {result := c, restSize := n - c.utf8Size, witness := by omega}
    | none => failure {error := Error.eof, restSize := n}
  sound t := by simp

/-- Like `gpure` but with a flexible grade: both `ge` and `gc` can be `never`
or `possibly`. Useful in match branches where all cases must share the same grade. -/
def ok (a : α) (he : ge ≤ possibly := by simp) (hc : gc ≤ possibly := by simp)
  : Parser ε ⟨ge, gc⟩ α where
  run {n} _ := success { result := a, restSize := n, witness := consumptionWitness.rfl hc }
  sound _ := he

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
  run {n} t := success <| match p.run t, p.sound t with
    | failure _, hs =>
      {result := .none, restSize := n, witness := consumptionWitness.rfl (inf_le_left.trans (Necessity.compl_le hs))}
    | success r, hs =>
      {result := .some r.result, restSize := r.restSize, witness := consumptionWitness.inf_of_possibly_le (Necessity.le_compl hs) r.witness}
  sound t := by simp only [Outcome.Sound]; decide

/-- Try `p`; return the result on success or the default value `d` on failure. -/
def optionalD (p : Parser ε ⟨ge, gc⟩ α) (d : α) : Parser ε ⟨never, ge.complement ⊓ gc⟩ α :=
  (·.getD d) <$>ᵍ optional p

/-- Try `p`; report whether it succeeded, never failing itself. -/
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
    let rec go {n} (t : Text n)
        : Success n possibly (List α) :=
      match p.run t with
      | .failure _ => {result := [], restSize := n}
      | .success r =>
        have : r.restSize < n := r.witness
        let rest := go (t.dropTo r.restSize r.le)
        {result := r.result :: rest.result
         restSize := rest.restSize
         witness := by have := rest.witness; omega}
    fun t => success (go t)
  sound t := by simp [Outcome.Sound]


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

/-- Parse `p` surrounded by the delimiters `l` and `r`. -/
def rawBracket (l r : Parser Error conditional PUnit) (p : Parser Error ⟨ge, gc⟩ α)
  : Parser Error ⟨ge ⊔ possibly, always⟩ α := gdo
  l
  let x ← p
  r
  return x
  grade_by by simp

/-- Parse `p` surrounded by the delimiters `l` and `r`. Delimiters consume whitespace after them. -/
def bracket (l r : Parser Error conditional PUnit) (p : Parser Error ⟨ge, gc⟩ α)
  : Parser Error ⟨ge ⊔ possibly, always⟩ α := rawBracket (lexeme l) (lexeme r) p

/-- Parse `p` surrounded by parentheses. -/
def parens (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge ⊔ possibly, always⟩ α := bracket lparen rparen p

/-- Parse `p` surrounded by square brackets. -/
def brackets (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge ⊔ possibly, always⟩ α := bracket lbracket rbracket p

/-- Parse `p` surrounded by curly braces. -/
def braces (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge ⊔ possibly, always⟩ α := bracket lbrace rbrace p

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

/-- Parse `sep` then `p`, returning `p`'s result; always consumes. -/
private def sepItem
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  (h : gc' ⊔ gc = always := by simp)
  : Parser ε ⟨ge' ⊔ ge, always⟩ α := gdo
  sep; p
  grade_by by simp [h]

/-- Parse zero or more occurrences of `p` separated by `sep`. -/
def sepBy
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  (h : gc' ⊔ gc = always := by simp)
  : Parser ε flexible (List α) := gdo
  let m ← optional p
  match m with
  | .some f =>
    let rest ← many (sepItem sep p h)
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
  let rest ← many (sepItem sep p h)
  return first ::₁ rest
  grade_by by simp

/-- Parse `p` then `sep`, returning `p`'s result; always consumes. -/
private def endItem
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  (h : gc ⊔ gc' = always := by simp)
  : Parser ε ⟨ge ⊔ ge', always⟩ α := gdo
  let x ← p; sep; return x
  grade_by by simp [h]

/-- Parse zero or more occurrences of `p`, each followed by `sep`. -/
def endBy
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  (h : gc ⊔ gc' = always := by simp)
  : Parser ε flexible (List α) :=
  many (endItem sep p h)

/-- Parse one or more occurrences of `p`, each followed by `sep`. -/
def endBy1
  (sep : Parser ε ⟨ge', gc'⟩ β)
  (p : Parser ε ⟨ge, gc⟩ α)
  (h : gc ⊔ gc' = always := by simp)
  : Parser ε ⟨ge ⊔ ge', always⟩ (NonEmptyList α) :=
  many1 (endItem sep p h)

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
  sound t := by simp

/-- Run `p` without consuming input, keeping only the result. -/
def lookahead (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge, never⟩ α :=
  p.handle
    (onSuccess := fun {n} _ h r => success {result := r.result, restSize := n})
    (soundSuccess := fun h _ => h)
    (onError := fun _ h f => failure f)
    (soundError := fun h _ => h)

def peek : Parser Error Grade.lookahead Char := lookahead anyChar

/-- Succeed (without consuming) only when `p` fails. -/
def notFollowedBy (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge.complement, never⟩ PUnit :=
  p.handle
    (onSuccess := fun _ h _ => Outcome.throw Error.fail)
    (soundSuccess := fun h _ => Necessity.le_compl h)
    (onError := fun {n} _ h _ => success {result := (), restSize := n})
    (soundError := fun h _ => Necessity.compl_le h)

/-- Run `p`; if it fails with error `e`, run `recover e`. If recovery also
fails, report `p`'s original error. -/
def withRecovery
  (recover : ε' → Parser ε ⟨ge, gc⟩ α)
  (p : Parser ε' ⟨ge', gc'⟩ α)
  : Parser ε' ⟨ge ⊓ ge', ge'.ite gc gc'⟩ α :=
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
