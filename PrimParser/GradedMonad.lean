import Mathlib.Algebra.Group.Defs

variable
  {G : Type} [Monoid G]

abbrev GradedType G := G → Type → Type

class GFunctor (f : GradedType G) : Type 1 where
  gmap {i α β} (h : α → β) : f i α → f i β

class GApplicative (f : GradedType G) extends GFunctor f where
  gpure {α} : α → f 1 α
  gseq {i j α β} : f i (α → β) → (Unit → f j α) → f (i * j) β

class GMonad (m : GradedType G) extends GApplicative m where
  gbind {i j α β} : m i α → (α → m j β) → m (i * j) β

syntax (name := gdoNotation) "gdo " doSeq : term

open Lean in
private partial def expandGDoBlock (doSeq : Syntax) : MacroM (TSyntax `term) := do
  let itemsNode := if doSeq.getKind == ``Lean.Parser.Term.doSeqIndent then
    doSeq[0]
  else
    doSeq[1]
  let elems := (itemsNode.getArgs.map fun item => item[0]).filter (!·.isMissing)
  if elems.isEmpty then
    Macro.throwError "empty gdo block"
  let last := elems.back!
  let init := elems.pop
  let r ← expandGDoFinal last
  let mut result := r
  for i in List.range init.size |>.reverse do
    result ← expandGDoElem init[i]! result
  return result
where
  expandGDoElem (elem : Syntax) (rest : TSyntax `term) : MacroM (TSyntax `term) :=
    match elem with
    | `(doElem| let $x:ident ← $e:term) => `(GMonad.gbind $e fun $x => $rest)
    | `(doElem| let $x:ident : $ty:term ← $e:term) => `(GMonad.gbind $e fun ($x : $ty) => $rest)
    | `(doElem| let $x:ident := $e:term) => `(let $x := $e; $rest)
    | `(doElem| let $x:ident : $ty:term := $e:term) => `(let $x : $ty := $e; $rest)
    | _ =>
      if elem.isOfKind ``Lean.Parser.Term.doMatch then do
        let matchTerm ← expandDoMatch elem
        `(GMonad.gbind $matchTerm fun _ => $rest)
      else
        let e : TSyntax `term := ⟨elem.getArgs.back!⟩
        `(GMonad.gbind $e fun _ => $rest)
  expandGDoFinal (elem : Syntax) : MacroM (TSyntax `term) := do
    match elem with
    | `(doElem| return $e:term) => `(GApplicative.gpure $e)
    | `(doElem| return) => `(GApplicative.gpure ())
    | _ =>
      if elem.isOfKind ``Lean.Parser.Term.doMatch then
        expandDoMatch elem
      else
        pure ⟨elem.getArgs.back!⟩
  expandDoMatch (node : Syntax) : MacroM (TSyntax `term) := do
    let processed ← replaceDoSeqs node
    return ⟨match processed with
      | .node info _ args => .node info ``Lean.Parser.Term.match args
      | other => other⟩
  replaceDoSeqs (node : Syntax) : MacroM Syntax := do
    if node.getKind == ``Lean.Parser.Term.doSeqIndent ||
       node.getKind == `Lean.Parser.Term.doSeqBrack then
      return (← expandGDoBlock node).raw
    let newArgs ← node.getArgs.mapM fun child => do
      if child.isAtom || child.isMissing then return child
      else replaceDoSeqs child
    return node.setArgs newArgs

open Lean in
@[macro gdoNotation] def expandGDo : Macro := fun stx => do
  expandGDoBlock stx[1]

section GDoExamples

variable
  {M : GradedType G} [GMonad M]
  {α β γ : Type} {i j k : G}

example (a : α) : M 1 α :=
  gdo return a

example (x : M i α) (f : α → M j β) : M (i * j) β :=
  gdo
    let a ← x
    f a

example (x : M i α) (f : α → M j β) (g : β → M k γ) : M (i * (j * k)) γ :=
  gdo
    let a ← x
    let b ← f a
    g b

example (x : M i α) (y : M j β) : M (i * j) β :=
  gdo
    x
    y

example (x : M i Nat) : M (i * 1) Nat :=
  gdo
    let a ← x
    return a + 1

example (x : M i (Option α)) (f : α → M j β) (e : M j β) : M (i * j) β :=
  gdo
    let a ← x
    match a with
    | .some b => f b
    | .none => e

example (x : M i (Option Nat)) : M (i * 1) Nat :=
  gdo
    let a ← x
    match a with
    | .some n => return n
    | .none => return 0

end GDoExamples
