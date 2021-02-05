import Lean.Expr
import Lean.Elab
import IIT.Util
open Lean
open Elab
open Meta

namespace Lean

namespace Meta

instance : Inhabited CasesSubgoal := Inhabited.mk $ CasesSubgoal.mk arbitrary ""

def clarifyIndex (mVar : MVarId) (fVar : FVarId) (i : Nat := 0) : MetaM MVarId := -- should be MetaM (MVarId × FVarSubst)
  withMVarContext mVar do
    let lctx       ← getLCtx
    let localInsts ← getLocalInstances
    checkNotAssigned mVar `generalizeIndices
    let fvarDecl ← getLocalDecl fVar
    let type ← whnf fvarDecl.type
    let failEx := fun _ => throwTacticEx `clarifyIndices mVar "inductive type expected"
    type.withApp fun f args => matchConstInduct f failEx fun val _ => do
      let I := args.get! (val.numParams + i)
      unless I.isFVar do return mVar --consider failing instead
      let IName := (← getLocalDecl I.fvarId!).userName
      let IType ← inferType I
      let r ← mkFreshExprMVar IType
      let eq ← mkEq r I
      let (eqMVar, (eqFVar, bodyMVar), mVarVal) ← metaHave mVar "eq" eq
      withMVarContext eqMVar do
        let eqSubgoals ← cases eqMVar fVar
        unless eqSubgoals.size == 1 do throwTacticEx `clarifyIndices eqMVar "indices must determine constructor uniquely"
        let rhs := eqSubgoals[0].subst.apply I
        let rhsType ← inferType rhs
        let u       ← getLevel rhsType
        let val := mkApp2 (mkConst `Eq.refl [u]) rhsType rhs
        assignExprMVar r.mvarId! rhs
        assignExprMVar eqSubgoals[0].mvarId val
      assignExprMVar mVar (← instantiateMVars mVarVal)
      withMVarContext bodyMVar do
        return bodyMVar

def clarifyIndices (mVar : MVarId) (fVar : FVarId) : MetaM MVarId := -- should be MetaM (MVarId × FVarSubst)
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

--set_option trace.Elab true
def bar (x : Fin 5) (p : Foo 5 x) (A : Type) (a : Foo 5 0 → A) : A := by
  clarifyIndices p
  cases eq





  
  




