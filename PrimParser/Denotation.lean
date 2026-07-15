import PrimParser.Basic
import PrimParser.Properties

/-!
# Denotational characterizations (`*_run` lemmas)

Extensional specs relating a concrete parser's `run` to a declarative
description of its behavior, in the spirit of mathlib's `parser.nat_eq_done`.
-/

namespace Parser

variable {α β ε : Type} {n : Nat} {ge gc : Necessity}

theorem anyChar_run_succ {m : Nat} (c : Char) (cs : List Char) (p : (c :: cs).length = m + 1) :
    anyChar.run (⟨c :: cs, p⟩ : Text (m + 1))
      = .inr { result := c, restSize := m, restText := ⟨cs, by simpa using p⟩, witness := by simp } := by
  rfl

theorem anyChar_run_zero (p : ([] : List Char).length = 0) :
    anyChar.run (⟨[], p⟩ : Text 0)
      = .inl { error := Error.eof, restText := ⟨[], p⟩, witness := by simp } := by
  rfl

/-- Two successes at the same input position are equal when their result and
remaining text (as a list) agree. `restSize` is forced by `restText`, and the
`witness` is a `Prop`. -/
theorem Success.ext' {n : Nat} {c : Necessity} {γ : Type} {s r : Success n c γ}
    (hres : s.result = r.result) (hrt : s.restText.toList = r.restText.toList) : s = r := by
  obtain ⟨sres, srest, sw⟩ := s
  obtain ⟨rres, rrest, rw⟩ := r
  obtain ⟨srl, srp⟩ := srest
  obtain ⟨rrl, rrp⟩ := rrest
  simp only [List.Vector.toList] at hrt
  subst hres; subst hrt; subst srp; subst rrp; rfl

/-- `digit` succeeds iff the input is nonempty with a leading digit; the value
is that digit and the remaining text is the tail. -/
theorem digit_run {n : Nat} (t : Text n) (r : Success n always Nat) :
    digit.run t = .inr r ↔
      ∃ c : Char, t.toList = c :: r.restText.toList ∧ c.isDigit = true ∧
        r.result = c.toNat - '0'.toNat := by
  obtain ⟨l, hl⟩ := t
  subst hl
  match l with
  | [] =>
    simp only [digit, token, GradedMonad.gbind, bind, anyChar_run_zero]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨c, hc, _⟩; simp [List.Vector.toList] at hc
  | c :: cs =>
    have hany : anyChar.run (⟨c :: cs, rfl⟩ : Text (cs.length + 1))
      = .inr { result := c, restSize := cs.length, restText := ⟨cs, rfl⟩, witness := by simp } :=
      anyChar_run_succ c cs rfl
    simp only [digit, token, GradedMonad.gbind, bind, hany]
    by_cases hd : c.isDigit = true
    · simp only [hd, if_true, ok, weakenErrors, gpure, pure, onOutcome, Outcome.handle,
        Outcome.ofSuccess, Success.seq, List.Vector.toList]
      constructor
      · rintro h
        have he := Sum.inr.inj h
        refine ⟨c, ?_, hd, ?_⟩ <;> rw [← he]
      · rintro ⟨c', hcs, _, hres⟩
        obtain ⟨rfl, hrest⟩ := List.cons.injEq .. ▸ hcs
        exact congrArg Sum.inr (Success.ext' (by simpa using hres.symm) (by simpa using hrest))
    · simp only [hd, Bool.false_eq_true, if_false, throw, Outcome.throw, Outcome.throwFailure]
      constructor
      · exact fun h => absurd h (by simp)
      · rintro ⟨c', hcs, hc', _⟩
        obtain ⟨rfl, _⟩ := List.cons.injEq .. ▸ hcs
        exact absurd hc' hd

/-- `runOption` is just `run` with the failure discarded. Stated separately
because `runOption` goes through the dependent `Outcome.handle`. -/
theorem runOption_eq {gc : Necessity} (p : Parser ε ⟨ge, gc⟩ α) (t : Text n) :
    p.runOption t = match p.run t with | .inl _ => none | .inr r => some r := by
  unfold runOption Outcome.handle
  split <;> simp_all

/-- `digit` fails (as an `Option`) iff the input has no leading digit
(covers the empty case vacuously). -/
theorem digit_runOption_none {n : Nat} (t : Text n) :
    digit.runOption t = none ↔ ∀ c cs, t.toList = c :: cs → c.isDigit = false := by
  rw [runOption_eq]
  obtain ⟨l, hl⟩ := t; subst hl
  match l with
  | [] =>
    simp [digit, token, GradedMonad.gbind, bind, anyChar_run_zero, List.Vector.toList]
  | c :: cs =>
    have hany := anyChar_run_succ c cs rfl
    simp only [digit, token, GradedMonad.gbind, bind, hany, List.Vector.toList]
    by_cases hd : c.isDigit = true <;>
      simp [hd, ok, weakenErrors, gpure, pure, onOutcome, Outcome.handle, Outcome.ofSuccess,
        Success.seq, throw, Outcome.throw, Outcome.throwFailure]

/-!
## `many` characterization

`many p` (for `p` that always consumes) is defined by the well-founded
recursion `many.go`. The three facts below pin it down:
* `many_run_eq` — running `many p` is exactly `many.go`, never failing;
* `many_go_unfold` — the one-step recursion equation;
* `many_go_maximal` — **maximal munch**: `p` cannot proceed on the leftover.
-/

theorem many_run_eq (p : Parser ε ⟨ge, always⟩ α) {n : Nat} (t : Text n) :
    (many p).run t = .inr (many.go p t) := rfl

theorem many_go_unfold (p : Parser ε ⟨ge, always⟩ α) {n : Nat} (t : Text n) :
    many.go p t = match p.runOption t with
      | .none => ⟨[], t, by simp⟩
      | .some r => ⟨r.result :: (many.go p r.restText).result,
                    (many.go p r.restText).restText,
                    by have := (many.go p r.restText).le; have := r.le
                       simp only [consumptionWitness]; omega⟩ := by
  rw [many.go.eq_def]; rfl

theorem many_go_maximal (p : Parser ε ⟨ge, always⟩ α) :
    ∀ {n : Nat} (t : Text n), p.runOption (many.go p t).restText = none := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t
    rw [many.go.eq_def]
    cases h : p.runOption t with
    | none => simpa using h
    | some r => exact ih r.restSize r.witness r.restText

/-- Capstone: after `many digit`, the leftover text has no leading digit —
concrete maximal munch, from the generic `many_go_maximal` and `digit_runOption_none`.
This is the missing half of a `nat_eq_done`-style spec; the value half follows
by induction on the collected digit list. -/
theorem manyDigit_maximal {n : Nat} (t : Text n) (c : Char) (cs : List Char)
    (h : (many.go digit t).restText.toList = c :: cs) : c.isDigit = false :=
  (digit_runOption_none _).mp (many_go_maximal digit t) c cs h

theorem runOption_some_iff {gc : Necessity} (p : Parser ε ⟨ge, gc⟩ α) (t : Text n)
    (r : Success n gc α) : p.runOption t = some r ↔ p.run t = .inr r := by
  rw [runOption_eq]; cases p.run t <;> simp

/-- `many digit` consumes exactly a maximal run of digits: there is a prefix
`pre` of all-digit characters with `t = pre ++ leftover` and the collected
results are the digit values of `pre`. (Maximality of the leftover is the
separate `manyDigit_maximal`.) -/
theorem manyDigit_go_spec : ∀ {n : Nat} (t : Text n),
    ∃ pre : List Char,
      (∀ c ∈ pre, c.isDigit = true) ∧
      t.toList = pre ++ (many.go digit t).restText.toList ∧
      (many.go digit t).result = pre.map (fun c => c.toNat - '0'.toNat) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t
    rw [many_go_unfold]
    cases hopt : digit.runOption t with
    | none => exact ⟨[], by simp, by simp, by simp⟩
    | some r =>
      have hrun : digit.run t = .inr r := (runOption_some_iff _ _ _).mp hopt
      obtain ⟨c, hcons, hcd, hcval⟩ := (digit_run t r).mp hrun
      obtain ⟨pre', hpre'd, hpre'app, hpre'val⟩ := ih r.restSize r.witness r.restText
      simp only []
      refine ⟨c :: pre', ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hcd
        · exact hpre'd x hx
      · rw [hcons, hpre'app, List.cons_append]
      · rw [List.map_cons, hcval, hpre'val]

/-- A maximal digit prefix is unique: if two all-digit prefixes are each
followed by text with no leading digit and the concatenations agree, the
splits agree. This is what makes the `nat_run` characterization an `iff`. -/
theorem digit_prefix_unique : ∀ (a b x y : List Char),
    (∀ c ∈ a, c.isDigit = true) → (∀ c ∈ b, c.isDigit = true) →
    (∀ c cs, x = c :: cs → c.isDigit = false) →
    (∀ c cs, y = c :: cs → c.isDigit = false) →
    a ++ x = b ++ y → a = b ∧ x = y := by
  intro a
  induction a with
  | nil =>
    intro b x y _ hb hx _ h
    cases b with
    | nil => simpa using h
    | cons d ds =>
      rw [List.nil_append, List.cons_append] at h
      exact absurd (hb d (by simp)) (by simp [hx d _ h])
  | cons c cs ih =>
    intro b x y ha hb hx hy h
    cases b with
    | nil =>
      rw [List.cons_append, List.nil_append] at h
      exact absurd (ha c (by simp)) (by simp [hy c _ h.symm])
    | cons d ds =>
      rw [List.cons_append, List.cons_append] at h
      obtain ⟨rfl, hrest⟩ := List.cons.injEq .. ▸ h
      obtain ⟨h1, h2⟩ := ih ds x y (fun z hz => ha z (by simp [hz])) (fun z hz => hb z (by simp [hz]))
        hx hy hrest
      exact ⟨by rw [h1], h2⟩

/-- Existential-prefix characterization of `nat.run`: succeeds iff the input
splits as a nonempty all-digit prefix followed by a leftover with no leading
digit, with the value the left-fold of the prefix. The `takeWhile`/`dropWhile`
form (`nat_run`) is derived from this. -/
theorem nat_run_prefix {n : Nat} (t : Text n) (s : Success n always Nat) :
    nat.run t = .inr s ↔
      ∃ pre : List Char, pre ≠ [] ∧
        (∀ c ∈ pre, c.isDigit = true) ∧
        (∀ c cs, s.restText.toList = c :: cs → c.isDigit = false) ∧
        t.toList = pre ++ s.restText.toList ∧
        s.result = pre.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 := by
  conv_lhs => unfold nat
  simp only [GradedMonad.gbind, gpure, Parser.bind, Parser.pure, Outcome.ofSuccess, many_run_eq]
  cases hdig : digit.run t with
  | inl f =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨pre, hne, hpred, _, happ, _⟩
    obtain ⟨c₀, pre', rfl⟩ := List.exists_cons_of_ne_nil hne
    have hno := (digit_runOption_none t).mp (by rw [runOption_eq, hdig])
    rw [List.cons_append] at happ
    have h1 := hpred c₀ (by simp)
    have h2 := hno c₀ _ happ
    simp_all
  | inr x =>
    obtain ⟨c₀, hcons, hc₀d, hxval⟩ := (digit_run t x).mp hdig
    obtain ⟨pre', hpre'd, hpre'app, hpre'val⟩ := manyDigit_go_spec x.restText
    -- value of the maximal digit run, in the two equivalent shapes
    have hval : (c₀ :: pre').foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
        = List.foldl (fun acc d => acc * 10 + d) x.result (many.go digit x.restText).result := by
      rw [hxval, hpre'val]; simp [List.foldl_map]
    have hmax := manyDigit_maximal x.restText
    simp only [Sum.inr.injEq]
    constructor
    · intro heq; subst heq
      refine ⟨c₀ :: pre', by simp, ?_, ?_, ?_, ?_⟩
      · intro z hz; rcases List.mem_cons.mp hz with rfl | hz
        · exact hc₀d
        · exact hpre'd z hz
      · simpa only [Success.seq_restText] using hmax
      · simp only [Success.seq_restText]
        rw [hcons, hpre'app, List.cons_append]
      · simpa only [Success.seq_result] using hval.symm
    · rintro ⟨pre, hne, hpred, hsmax, happ, hsval⟩
      have happ' : pre ++ s.restText.toList
          = (c₀ :: pre') ++ (many.go digit x.restText).restText.toList := by
        rw [← happ, hcons, hpre'app, List.cons_append]
      obtain ⟨hpre_eq, hrest_eq⟩ := digit_prefix_unique pre (c₀ :: pre') _ _ hpred
        (fun z hz => by rcases List.mem_cons.mp hz with rfl | hz; exacts [hc₀d, hpre'd z hz])
        hsmax hmax happ'
      refine Success.ext' ?_ ?_
      · simp only [Success.seq_result]
        rw [hsval, hpre_eq]; exact hval.symm
      · simpa only [Success.seq_restText] using hrest_eq.symm

/-- `nat.run` in closed `takeWhile`/`dropWhile` form: succeeds iff there is a
leading digit, consuming exactly the maximal digit prefix and leaving the rest,
with the value the left-fold of that prefix. -/
theorem nat_run {n : Nat} (t : Text n) (s : Success n always Nat) :
    nat.run t = .inr s ↔
      t.toList.takeWhile (·.isDigit) ≠ [] ∧
      s.restText.toList = t.toList.dropWhile (·.isDigit) ∧
      s.result = (t.toList.takeWhile (·.isDigit)).foldl
        (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 := by
  rw [nat_run_prefix]
  constructor
  · rintro ⟨pre, hne, hpred, hmax, happ, hval⟩
    have htake : t.toList.takeWhile (·.isDigit) = pre := by
      rw [happ, List.takeWhile_append_of_pos hpred]
      rcases hrest : s.restText.toList with _ | ⟨c, cs⟩
      · simp
      · simp [hmax c cs hrest]
    have hdrop : t.toList.dropWhile (·.isDigit) = s.restText.toList := by
      rw [happ, List.dropWhile_append_of_pos hpred]
      rcases hrest : s.restText.toList with _ | ⟨c, cs⟩
      · simp
      · simp [hmax c cs hrest]
    exact ⟨htake ▸ hne, hdrop.symm, htake ▸ hval⟩
  · rintro ⟨hne, hrest, hval⟩
    refine ⟨t.toList.takeWhile (·.isDigit), hne,
      fun c hc => List.all_eq_true.mp List.all_takeWhile c hc, ?_, ?_, hval⟩
    · intro c cs hcs
      have h := List.head?_dropWhile_not (·.isDigit) t.toList
      rw [← hrest, hcs] at h
      simpa using h
    · rw [hrest, List.takeWhile_append_dropWhile]

end Parser
