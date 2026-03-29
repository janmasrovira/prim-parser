import PrimParser.GradedMonad.Basic

/-!
# Graded Do-Notation

Provides `gdo` blocks that desugar into `gbind`/`gpure` calls, mirroring
Lean's built-in `do` notation for graded monads. An optional trailing
`grade_by` element supplies a proof that the computed grade equals the
expected one.
-/

variable
  {G : Type} [Monoid G]

syntax "grade_by " term : doElem

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
  let (mainElems, castProof) ← do
    match elems.back! with
    | `(doElem| grade_by $proof:term) => pure (elems.pop, some proof)
    | _ => pure (elems, none)
  if mainElems.isEmpty then
    Macro.throwError "empty gdo block (only grade_by)"
  let last := mainElems.back!
  let init := mainElems.pop
  let r ← expandGDoFinal last
  let mut result := r
  for i in List.range init.size |>.reverse do
    result ← expandGDoElem init[i]! result
  match castProof with
  | some proof => `(gcast $proof $result)
  | none => return result
where
  expandGDoElem (elem : Syntax) (rest : TSyntax `term) : MacroM (TSyntax `term) :=
    match elem with
    | `(doElem| let $x:ident ← $e:term) => `(GMonad.gbind $e fun $x => $rest)
    | `(doElem| let _ ← $e:term) => `(GMonad.gbind $e fun _ => $rest)
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

example (x : M i α) : M i α :=
  gdo
    let a ← x
    return a
    grade_by by simp

example (x : M i α) (y : M j β) : M (i * j) β :=
  gdo
    let _ ← x
    y

end GDoExamples
