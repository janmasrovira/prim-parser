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

/-- Relates input size `n` and remaining size `m` according to a consumption grade:
`always` requires strict decrease, `possibly` allows `≤`, `never` requires equality. -/
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

/-- A successful parse result -/
structure Success (n : Nat) (consumes : Necessity) (α : Type) where
  result : α
  {restSize : Nat}
  restText : Text restSize
  witness : consumptionWitness restSize n consumes := by simp

/-- The result type of running a parser -/
abbrev Outcome (ε : Type) (n : Nat) (g : Grade) (α : Type) : Type :=
  match g.errors with
  | .never => Success n g.consumes α
  | .possibly => ε ⊕ Success n g.consumes α
  | .always => ε

end Parser

/-- A parser with error type `ε`, static grade `g`, and result type `α`.
The grade tracks error and consumption behavior at the type level. -/
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

/-- Monadic bind for parsers. The resulting grade is the product (max)
of the two grades. -/
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

/-- Lift a value into a parser that consumes nothing and never fails. -/
abbrev pure (a : α) : Parser ε 1 α where
  run t := ⟨a, t, rfl⟩

instance : GApplicative (Parser ε) where
  gpure := pure
  gseq f g := bind f fun f' => ⟨fun t => f' <$> (g ()).run t⟩

instance : GMonad (Parser ε) where
  gbind := bind

/-- Build a recursive parser via a fixpoint. Termination is guaranteed by
requiring the body to always consume input. -/
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
  ⟨fun t => go t⟩

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

/-- Try `p1`; if it fails, try `p2`. The error grade is the infimum and
the consumption grade is computed via `Necessity.ite`. -/
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

infixl:20 " <|> " => choice

/-- Try each parser in the list in order, returning the first success. -/
def oneOf (l : List (Parser ε g α)) (p : l.length ≠ 0 := by simp) : Parser ε g α := match l with
  | [] => nomatch p
  | [x] => x
  | x :: y :: xs => by refine cast ?_ (choice x (oneOf (y :: xs)))
                       congr 2 <;> simp

/-- A parser that always fails with error `e`. -/
def throw (e : ε) (c : .possibly ≤ ge := by simp) : Parser ε ⟨ge, gc⟩ α where
  run _ := Outcome.throw (h := c) e

def Success.relaxConsumes (p : Success n gc α) : Success n (gc ⊓ .possibly) α :=
  match gc with
  | .never => p
  | .possibly => p
  | .always => { p with witness := le_of_lt p.witness }

/-- Weaken the consumption grade by capping at `possibly`. -/
def relaxConsumes (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge, gc ⊓ .possibly⟩ α where
  run t :=
    (p.run t).handle
      (fun h e => Outcome.throw (h := h) e)
      (fun h r => Outcome.ofSuccess (c := h) r.relaxConsumes)

/-- Weaken the error grade by capping at `possibly`. -/
def relaxErrors (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge ⊓ .possibly, gc⟩ α where
  run t :=
    (p.run t).handle
      (fun h e => Outcome.throw (h := le_inf h le_rfl) e)
      (fun _ r => Outcome.ofSuccess (c := inf_le_right) r)

/-- Cap both error and consumption grades at `possibly`. -/
def relax (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge ⊓ .possibly, gc ⊓ .possibly⟩ α :=
  p.relaxErrors.relaxConsumes

def Success.weakenConsumes (p : Success n gc α) : Success n .possibly α :=
  match gc with
  | .never => { p with witness := le_of_eq p.witness }
  | .possibly => p
  | .always => { p with witness := le_of_lt p.witness }

/-- Forget consumption precision, setting it to `possibly`. -/
def weakenConsumes (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨ge, .possibly⟩ α where
  run t :=
    (p.run t).handle
      (fun h e => Outcome.throw (h := h) e)
      (fun h r => Outcome.ofSuccess (c := h) r.weakenConsumes)

/-- Forget error precision, setting it to `possibly`. -/
def weakenErrors (p : Parser ε ⟨ge, gc⟩ α) : Parser ε ⟨.possibly, gc⟩ α where
  run t :=
    (p.run t).handle
      (fun _ e => .inl e)
      (fun _ r => .inr r)

/-- Weaken both grades to `possibly`, yielding a `fallible` parser. -/
def weaken (p : Parser ε ⟨ge, gc⟩ α) : Parser ε .fallible α :=
  p.weakenErrors.weakenConsumes

/-- Run a parser, discarding the error and returning the `Success` as an `Option`. -/
def runOption (p : Parser ε ⟨ge, gc⟩ α) (t : Text n) : Option (Success n gc α) :=
  p.run t |>.handle (fun _ _ => .none) (fun _ r => .some r)

/-- Run a parser, returning only the parsed value as an `Option`. -/
def runResult? (p : Parser ε ⟨ge, gc⟩ α) (t : Text n) : Option α :=
  p.run t |>.handle (fun _ _ => .none) (fun _ r => .some r.result)

/-- Consume and return a single character, or fail on empty input. -/
def anyChar : Parser Error .conditional Char where
  run {n} t :=
    match n, t with
    | 0, .nil => .inl Error.eof
    | Nat.succ n, ⟨c :: cs, p⟩ =>
      .inr {result := c
            restSize := n
            restText := by refine ⟨cs, by simpa [List.length_cons] using p⟩
            witness := by simp}

/-- Like `gpure` but with a flexible grade: both `ge` and `gc` can be `never`
or `possibly`. Useful in match branches where all cases must share the same grade. -/
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

/-- Consume a character and apply `f`; succeed with the result or fail if `f` returns `none`. -/
def token (f : Char → Option α) : Parser Error .conditional α := gdo
  let c ← anyChar
  match f c with
  | .some r => ok (gc := .never) r
  | .none => throw (ge := .possibly) Error.fail

/-- Consume a character that satisfies predicate `f`, or fail. -/
def satisfy (f : Char → Bool) : Parser Error .conditional Char :=
  token (fun c => if f c then .some c else .none)

/-- Match a specific character. -/
def char (c : Char) : Parser Error .conditional PUnit :=
  () <$ᵍ satisfy (· == c)

/-- Match an exact string. -/
def string (str : String) : Parser Error .conditional PUnit :=
  let rec go : List Char → Parser Error .conditional PUnit
    | [] => throw Error.fail
    | [c] => () <$ᵍ satisfy (· == c)
    | c :: cs => gdo
      satisfy (· == c)
      go cs
  go str.toList

/-- Try `p`; return `some result` on success or `none` on failure, never failing itself. -/
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

/-- Try `p`; return the result on success or the default value `d` on failure. -/
def optionalD (p : Parser ε ⟨ge, gc⟩ α) (d : α) : Parser ε ⟨.never, ge.complement ⊓ gc⟩ α :=
  (·.getD d) <$>ᵍ optional p

/-- Try `p` then apply `cont` to its result; wrap the final result in `Option`. -/
def optionalBind
  (p : Parser ε ⟨ge, gc⟩ α)
  (cont : α → Parser ε ⟨ge', gc'⟩ β)
  : Parser ε ⟨.never, (ge ⊔ ge').complement ⊓ (gc ⊔ gc')⟩ (Option β) :=
  optional (gdo
    let a ← p
    cont a
    grade_by by simp)

/-- Repeatedly apply `p` until `e` succeeds, collecting the results of `p`. -/
def manyTill [Inhabited ε]
  (p : Parser ε ⟨ge, .always⟩ α)
  (e : Parser ε ⟨ge', .always⟩ β)
  : Parser ε ⟨ge, .always⟩ (List α) :=
  match ge with
  | .always => (fun x => [x]) <$>ᵍ p
  | .never => IsEmpty.false p |>.elim
  | .possibly =>
      fix fun self =>
        oneOf [
          [] <$ᵍ e |>.weakenErrors,
          gdo let a ← p; let as ← self; return (a :: as); grade_by by simp
        ]

/-- Apply `p` zero or more times, collecting results. Requires `p` to always consume. -/
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

abbrev NonEmptyList α := { l : List α // l ≠ [] }
abbrev NonEmptyList.mk (x : α) (xs : List α) : NonEmptyList α := ⟨x :: xs, by simp⟩
abbrev NonEmptyList.toList : NonEmptyList α → List α := (·.1)
infixr:67 " ::₁ " => NonEmptyList.mk

/-- Apply `p` one or more times, collecting results. -/
def many1 (p : Parser ε ⟨ge, .always⟩ α) : Parser ε ⟨ge, .always⟩ (NonEmptyList α) := gdo
  let x ← p
  let xs ← many p
  return x ::₁ xs
  grade_by by simp

/-- Consume characters while `f` holds, returning the collected string. -/
def takeWhile (f : Char → Bool) : Parser Error .flexible String :=
  String.ofList <$>ᵍ many (satisfy f)

/-- Consume one or more characters while `f` holds. -/
def takeWhile1 (f : Char → Bool) : Parser Error .conditional String :=
  (String.ofList ∘ NonEmptyList.toList) <$>ᵍ many1 (satisfy f)

/-- Skip characters while `f` holds. -/
def skipWhile (f : Char → Bool) : Parser Error .flexible PUnit :=
  () <$ᵍ takeWhile f

/-- Skip one or more characters while `f` holds. -/
def skipWhile1 (f : Char → Bool) : Parser Error .conditional PUnit :=
  () <$ᵍ takeWhile1 f

/-- Skip zero or more whitespace characters. -/
def whitespace : Parser Error .flexible PUnit :=
  skipWhile Char.isWhitespace

/-- Skip one or more whitespace characters. -/
def whitespace1 : Parser Error .conditional PUnit :=
  skipWhile1 Char.isWhitespace

/-- Run `p` then skip trailing whitespace. -/
def lexeme (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge, gc ⊔ .possibly⟩ α := gdo
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
def parens (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge ⊔ .possibly, .always⟩ α := gdo
  lexeme lparen; let r ← p; lexeme rparen; return r
  grade_by by simp

/-- Parse `p` surrounded by square brackets. -/
def brackets (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge ⊔ .possibly, .always⟩ α := gdo
  lexeme lbracket; let r ← p; lexeme rbracket; return r
  grade_by by simp

/-- Parse `p` surrounded by curly braces. -/
def braces (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge ⊔ .possibly, .always⟩ α := gdo
  lexeme lbrace; let r ← p; lexeme rbrace; return r
  grade_by by simp

/-- Parse a single decimal digit, returning its numeric value. -/
def digit : Parser Error .conditional Nat :=
  token fun c => if c.isDigit then some (c.toNat - '0'.toNat) else none

/-- Parse a natural number (one or more digits). -/
def nat : Parser Error .conditional Nat := gdo
  let d ← digit
  let ds ← many digit
  return ds.foldl (fun acc d => acc * 10 + d) d

/-- Parse an integer (optional leading `-` followed by digits). -/
def int : Parser Error .conditional Int := gdo
  let neg ← optional (char '-')
  let n ← nat
  return if neg.isSome then -n else n
  grade_by by simp

/-- Parse zero or more occurrences of `p` separated by `sep`. -/
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

/-- Parse exactly `n + 1` occurrences of `p`. -/
def countSucc
  (p : Parser ε ⟨ge, gc⟩ α)
  : (n : Nat) → Parser ε ⟨ge, gc⟩ (List.Vector α (n + 1))
  | 0 => (· ::ᵥ .nil) <$>ᵍ p
  | n + 1 => gdo
      let x ← p
      let rest ← countSucc p n
      return (x ::ᵥ rest)
      grade_by by simp

/-- Parse exactly `n` occurrences of `p`. -/
def count
  (p : Parser ε ⟨ge, gc⟩ α)
  : (n : Nat) → Parser ε ⟨ge ⊓ .possibly, gc ⊓ .possibly⟩ (List.Vector α n)
  | 0 => ok .nil
  | n + 1 => countSucc p n |>.relax

/-- Parse exactly `n` occurrences of `p` separated by `sep`. -/
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

/-- Parse one or more occurrences of `p` separated by left-associative operator `op`. -/
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

/-- Succeed only at end of input, consuming nothing. -/
def eof : Parser Error .lookahead PUnit where
  run {n} t := match n with
   | .zero => ok () |>.run t
   | _ => throw Error.fail |>.run t

/-- Run `p` without consuming input, keeping only the result. -/
def lookahead (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge, .never⟩ α where
  run t := p.run t |>.handle
    (fun h e => Outcome.throw (h := h) e)
    (fun h r => Outcome.ofSuccess (c := h) {result := r.result, restText := t})

/-- Succeed (without consuming) only when `p` fails. -/
def notFollowedBy (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge.complement, .never⟩ PUnit where
  run t := p.run t |>.handle
    (fun _ _ => Outcome.ofSuccess (c := by cases ge <;> first | contradiction | decide) {result := (), restText := t})
    (fun _ _ => Outcome.throw (h := by cases ge <;> first | contradiction | decide) Error.fail)

/-- Run `p`; if it fails with error `e`, run `recover e`. If recovery also
fails, report `p`'s original error. -/
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
