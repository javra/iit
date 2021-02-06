import Lean.Expr
import Lean.Elab
import IIT.Util
open Lean
open Elab
open Meta

namespace Lean

namespace Meta

instance : Inhabited CasesSubgoal := Inhabited.mk $ CasesSubgoal.mk arbitrary ""

def clarifyIndex (mVar : MVarId) (fVar : FVarId) (i : Nat := 0) : MetaM MVarId :=
  withMVarContext mVar do
    let fvarDecl ← getLocalDecl fVar
    let type ← whnf fvarDecl.type
    let failEx := fun _ => throwTacticEx `clarifyIndices mVar "inductive type expected"
    type.withApp fun f args => matchConstInduct f failEx fun val _ => do
      let I := args.get! (val.numParams + i)
      unless I.isFVar do return mVar --consider failing instead
      let IName := (← getLocalDecl I.fvarId!).userName
      let r ← mkFreshExprMVar $ ← inferType I
      let eq ← mkEq r I
      let (eqMVar, (eqFVar, bodyMVar), mVarVal) ← metaHave mVar "eq" eq
      let eqSubgoals ← cases eqMVar fVar
      unless eqSubgoals.size == 1 do throwTacticEx `clarifyIndices eqMVar "indices must determine constructor uniquely"
      let eqsg ← eqSubgoals[0].mvarId
      let rhs := eqSubgoals[0].subst.apply I
      let u       ← getLevel (← inferType rhs)     
      let val :=  mkApp2 (mkConst `rfl [u]) (← inferType rhs) rhs
      assignExprMVar r.mvarId! (← instantiateMVars rhs)
      assignExprMVar eqsg (← instantiateMVars val)
      assignExprMVar mVar (← instantiateMVars $ mVarVal)
      let gs ← cases bodyMVar eqFVar
      let mVar' ← clear gs[0].mvarId $ Expr.fvarId! $ gs[0].subst.apply $ mkFVar eqFVar
      withMVarContext mVar' do
        let unassignedMVars ← getMVars $ mkMVar eqMVar
        let unassignedMVarTypes : Array Expr ← unassignedMVars.mapM fun mid => getMVarType mid
        --throwTacticEx `clarifyIndices mVar' unassignedMVarTypes
        return mVar'

def clarifyIndices (mVar : MVarId) (fVar : FVarId) : MetaM MVarId :=
  withMVarContext mVar do
    let lctx       ← getLCtx
    let localInsts ← getLocalInstances
    checkNotAssigned mVar `generalizeIndices
    let fvarDecl ← getLocalDecl fVar
    let type ← whnf fvarDecl.type
    let failEx := fun _ => throwTacticEx `clarifyIndices mVar "inductive type expected"
    type.withApp fun f args => matchConstInduct f failEx fun val _ => do
      unless val.numIndices > 0 do throwTacticEx `clarifyIndices mVar "indexed inductive type expected"
      unless args.size == val.numIndices + val.numParams do throwTacticEx `clarifyIndices mVar "ill-formed inductive datatype"
      let mut mVar := mVar
      for i in [:val.numIndices] do
        mVar ← clarifyIndex mVar fVar i
      return mVar

end Meta

open Tactic

syntax (name := clarifyIndices) "clarifyIndices" (colGt ident)+ : tactic
@[tactic clarifyIndices] def elabClarifyIndices : Tactic
| `(tactic|clarifyIndices $fVars*) => do
  forEachVar fVars fun mVar fVar => do
  let tacResult ← Meta.clarifyIndices mVar fVar
  return tacResult --TODO
| _ => throwUnsupportedSyntax

end Lean

-- Example
inductive Foo : (n : Nat) → Fin n → Prop
| mk1 : Foo 5 0
| mk2 : Foo 8 3

--set_option pp.all true
def bar (x : Fin 5) (p : Foo 5 x) (A : Type) (a : Foo 5 0 → A) : A := by
  clarifyIndices p
  exact a p






  
  




