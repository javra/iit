import Lean

open Lean
open Elab
open Meta

namespace Lean

namespace Meta

instance : Inhabited CasesSubgoal := Inhabited.mk $ CasesSubgoal.mk arbitrary ""

def clarifyIndex (mVar : MVarId) (fVar : FVarId) (i : Nat := 0) : MetaM (FVarSubst × MVarId) :=
  withMVarContext mVar do
    let fvarDecl ← getLocalDecl fVar
    let type ← whnf fvarDecl.type
    let target ← getMVarType mVar
    let failEx := fun _ => throwTacticEx `clarifyIndices mVar "inductive type expected"
    type.withApp fun f args => matchConstInduct f failEx fun val _ => do
      let rhs := args.get! (val.numParams + i)
      unless rhs.isFVar do return (FVarSubst.empty, mVar) --consider failing instead
      let lhs ← mkFreshExprMVar $ ← inferType rhs
      let eqType ← mkEq lhs rhs
      -- First cases run to determine the lhs of the equation
      let eqSubgoals ← cases (← mkFreshExprMVar eqType).mvarId! fVar
      let eqsg := eqSubgoals[0].mvarId
      withMVarContext eqsg do assignExprMVar lhs.mvarId! $ eqSubgoals[0].subst.apply rhs
      let eqMVar ← mkFreshExprMVar eqType
      -- Second cases run to actually prove the equality
      let eqSubgoals ← cases eqMVar.mvarId! fVar
      if eqSubgoals.size == 0 then throwTacticEx `clarifyIndices eqMVar.mvarId! "tactic should now prove False and the target from it"
      unless eqSubgoals.size == 1 do throwTacticEx `clarifyIndices eqMVar.mvarId! "indices must determine constructor uniquely"
      let eqsg := eqSubgoals[0].mvarId
      withMVarContext eqsg do
        let u ← getLevel (← inferType lhs)
        assignExprMVar eqsg $ mkApp2 (mkConst `rfl [u]) (← inferType lhs) lhs
      -- Intro the equality as an fVar
      let fMVar ← mkFreshExprMVar $ mkForall "eq" BinderInfo.default eqType target
      assignExprMVar mVar $ mkApp fMVar (← instantiateMVars eqMVar)
      let (eqFVar, bodyMVar) ← intro fMVar.mvarId! "eq"
      withMVarContext bodyMVar do
        -- Apply cases on the equality
        let eqCases ← cases bodyMVar eqFVar
        unless eqCases.size == 1 do throwTacticEx `clarifyIndices bodyMVar "could not apply cases on resulting equality"
        let mVar' ← eqCases[0].mvarId
        withMVarContext mVar' do
          let mVar' ← clear mVar' $ Expr.fvarId! $ eqCases[0].subst.apply $ mkFVar eqFVar
          return (eqCases[0].subst, mVar')

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
      let mut fVar := fVar
      for i in [:val.numIndices] do
        let (subst, mVar') ← clarifyIndex mVar fVar i
        mVar := mVar'
        fVar := Expr.fvarId! $ subst.apply $ mkFVar fVar
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

inductive Foo' : (m n : Nat) → Fin (m + n) → Prop
| mk1 : Foo' 4 2 0
| mk2 : Foo' 1 3 1

def bar' (y : Nat) (x : Fin 6) (p : Foo' 4 2 x) (A : Type) (a : Foo' 4 2 0 → A) : A := by
  clarifyIndices p
  exact a p

inductive Foo'' : (m n l : Nat) → Prop
| mk1 : Foo'' 1 2 3
| mk2 : Foo'' 4 5 6

def bar'' (x y : Nat) (p : Foo'' x y 3) (h : x < y) : Foo'' x 2 3 := by
  clarifyIndices p
  exact p




  
  




