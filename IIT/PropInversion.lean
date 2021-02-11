import Lean
import IIT.Util

open Lean
open Elab
open Meta

namespace Lean

namespace Meta

def inversion (mVar : MVarId) (fVar : FVarId) : MetaM (Array FVarId × MVarId) :=
withMVarContext mVar do
  checkNotAssigned mVar `inversion
  let target ← getMVarType mVar
  -- Get Prop sorted fields
  let truesgs ← cases (← mkFreshExprMVar $ mkConst `True).mvarId! fVar
  unless truesgs.size == 1 do throwTacticEx `inversion mVar "indices must determine constructor uniquely"
  let trueMVar := truesgs[0].mvarId
  let fields   := truesgs[0].fields
  let fields ← withMVarContext trueMVar do
    let fields   ← fields.mapM fun e => inferType e
    fields.filterM fun e => do return (← getLevel e).isZero
  -- Prove fields
  let mut mVar       := mVar
  let mut fieldFVars := #[]
  for e in fields do
    let (fieldFVar, mVar') ← withMVarContext mVar do
      let fieldMVar ← mkFreshExprMVar e
      let fsgs ← cases fieldMVar.mvarId! fVar
      assumption fsgs[0].mvarId
      let fMVar ← mkFreshExprMVar $ mkForall Name.anonymous BinderInfo.default e target
      assignExprMVar mVar $ mkApp fMVar fieldMVar
      intro fMVar.mvarId! Name.anonymous
    mVar       := mVar'
    fieldFVars := fieldFVars.push fieldFVar
  return (fieldFVars, mVar)

end Meta

open Tactic

syntax (name := inversion) "inversion" (colGt ident)+ : tactic
@[tactic inversion] def elabInversion : Tactic
| `(tactic|inversion $fVars*) => do
  forEachVar fVars fun mVar fVar => do
  let (_, mVar) ← Meta.inversion mVar fVar
  return mVar
| _ => throwUnsupportedSyntax

end Lean

/-
-- Examples
inductive Foo : Nat → Nat → Prop
| mk1 : Foo 5 3
| mk2 : Foo 3 3 → Foo 9 8 → (n : Nat) → Foo 1 2

def bar (n : Nat) (x : Foo 1 n) (A : Type) (p : Foo 9 8 → A) : A := by
  inversion x
  apply p
  assumption
-/
