import Lean
import IIT.Util

open Lean
open Elab
open Meta

namespace Lean

namespace Meta

def inversion (mVar : MVarId) (fVar : FVarId) (names : Array Name) :
  MetaM (Array Name × Array FVarId × MVarId) :=
withMVarContext mVar do
  checkNotAssigned mVar `inversion
  let target ← getMVarType mVar
  -- Get Prop sorted fields
  let truesgs ← cases (← mkFreshExprMVar $ mkConst `True).mvarId! fVar
  unless truesgs.size == 1 do throwTacticEx `inversion mVar "indices must determine constructor uniquely"
  let trueMVar := truesgs[0].mvarId
  let fields   := truesgs[0].fields
  let fields ← withMVarContext trueMVar do
    let fields ← fields.mapM fun fv => do
       let fv ← whnf fv
       inferType fv
    fields.filterM fun e => do return (← getLevel e).isZero
  -- Prove fields
  let mut mVar       := mVar
  let mut fieldFVars := #[]
  let mut names      := names
  for (e : Expr) in fields do
    let (names',fieldFVar, mVar') ← withMVarContext mVar do
      let fieldMVar ← mkFreshExprMVar e
      let fsgs ← cases fieldMVar.mvarId! fVar
      assumption fsgs[0].mvarId
      let name := if names.size > 0 then names[0] else Name.anonymous
      let fMVar ← mkFreshExprMVar $ mkForall name BinderInfo.default e target
      assignExprMVar mVar $ mkApp fMVar fieldMVar
      let (fieldFVar, mVar') ← intro fMVar.mvarId! name
      pure (names[1:], fieldFVar, mVar')
    names      := names'
    mVar       := mVar'
    fieldFVars := fieldFVars.push fieldFVar
  return (names[1:], fieldFVars, mVar)

end Meta

open Tactic

syntax (name := inversion) "inversion" (colGt ident)+ ("with" (colGt ident)+)? : tactic
@[tactic inversion] def elabInversion : Tactic
| `(tactic|inversion $fVars* with $names*) => do
  let mut names := names.map getNameOfIdent'
  for f in fVars do
    let rnames ← withMainContext do
      let fvarId ← getFVarId f
      let (rnames, _, mVar) ← Meta.inversion (← getMainGoal) (← getFVarId f) names
      replaceMainGoal [mVar]
      pure rnames
    names := rnames
| `(tactic|inversion $fVars*) => do
  forEachVar fVars fun mVar fVar => do
  let (_, _, mVar) ← Meta.inversion mVar fVar #[]
  return mVar
| _ => throwUnsupportedSyntax

end Lean

/-
-- Examples
inductive Foo : Nat → Nat → Prop
| mk1 : Foo 5 3
| mk2 : (y : Foo 9 8) → (z : Foo 13 25) → Foo 1 2

example (n : Nat) (x : Foo 1 n) (A : Type) (p : (y : Foo 9 8) → A) : A := by
  inversion x with y z
  exact p y

example (n : Nat) (x : Foo (2 - 1) n) (A : Type) (p : (y : Foo 9 8) → A) : A := by
  skip
  inversion x
  apply p
  assumption
-/
