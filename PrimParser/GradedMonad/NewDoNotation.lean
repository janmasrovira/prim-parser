import Lean
import PrimParser.GradedMonad.Basic

/-!
# Graded Do-Notation

Provides a `gdo'` block that desugars into `gbind`/`gpure` calls, mirroring
Lean's built-in `do` notation for graded monads.
-/

open Lean Elab Term Meta Lean.Elab.Do

namespace GradedDo

syntax (name := gdoElab) "gdo' " doSeq : term

private def gradedOps (lctx : LocalContext) (insts : LocalInstances) (G M : Expr) : DoOps where
  mkMonadApp α : DoElabM Expr :=
    return mkApp2 M (← mkFreshExprMVarAt lctx insts G) α

  mkPureApp α e : DoElabM Expr :=
    mkAppOptM ``GradedApplicative.gpure #[none, none, none, M, none, α, e]

  mkBindApp _α _β e k : DoElabM Expr :=
    mkAppM ``GradedMonad.gbind #[e, k]

  isPureApp? e : Option Expr :=
    if e.isAppOfArity ``GradedApplicative.gpure 7 then some e.appArg! else none

  splitMonadApp? type : TermElabM (Option (MonadInfo × Expr)) := do
    let .app m resultType := type.consumeMData | return none
    return some ({ m, u := .zero, v := .zero }, resultType)

@[term_elab gdoElab] def elabGDo : TermElab := fun stx expectedType? => do
  let `(gdo' $doSeq) := stx | throwUnsupportedSyntax
  tryPostponeIfNoneOrMVar expectedType?
  let some (.app (.app M i) _α) ← expectedType?.mapM instantiateMVars
    | throwError "gdo' needs a known expected type of the form `M i α`"
  let ops := gradedOps (← getLCtx) (← getLocalInstances) (← inferType i) M
  elabDoWith ops doSeq expectedType?

end GradedDo

section Examples

variable
  {G : Type} [Monoid G]
  {M : GradedType G} [GradedMonad M]
  {α β γ : Type} {i j k : G}

example (a : α) : M 1 α :=
  gdo' return a

example (x : M i α) (f : α → M j β) : M (i * j) β :=
  gdo'
    let a ← x
    f a

example (x : M i α) (f : α → M j β) (g : β → M k γ) : M (i * (j * k)) γ :=
  gdo'
    let a ← x
    let b ← f a
    g b

example (x : M i Nat) : M (i * 1) Nat :=
  gdo'
    let a ← x
    return a + 1

example (x : M i (Option α)) (f : α → M j β) (e : M j β) : M (i * j) β :=
  gdo'
    let a ← x
    match a with
    | .some b => f b
    | .none => e

example (x : M i α) : M i α :=
  gdo'
    let a ← x
    return a

example (x : M i α) (y : M 1 β) : M i β :=
  gcast (by simp) (gdo'
    let _ ← x
    y)

example (x : M i Nat) : M (i * 1) Nat :=
  gdo'
    let n ← x
    if n == 0 then
      return 1
    else
      return n

example (x : M i Nat) : M (i * 1) Nat :=
  gdo'
    return (← x) + 1

example (x : M i (Nat × Nat)) : M (i * 1) Nat :=
  gdo'
    let (a, b) ← x
    return a + b

end Examples
