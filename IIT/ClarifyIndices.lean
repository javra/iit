import Lean

open Lean
open Elab
open Meta

namespace Lean

namespace Meta

instance : Inhabited CasesSubgoal := Inhabited.mk $ CasesSubgoal.mk arbitrary ""

def substituteWithCasesOn (mVar : MVarId) (fVar : FVarId) (e : Expr) : MetaM Expr :=
withMVarContext mVar do
  let eqSubgoals ← cases (← mkFreshExprMVar $ mkConst `True).mvarId! fVar
  return eqSubgoals[0].subst.apply e

def clarifyIndexFalse (mVar : MVarId) (fVar : FVarId) (i : Nat) : MetaM Unit :=
withMVarContext mVar do
  let falseMVar ← mkFreshExprMVar $ mkConst `False
  let eqSubgoals ← cases falseMVar.mvarId! fVar
  unless eqSubgoals.size == 0 do throwTacticEx `clarifyIndices mVar "something wrong here"
  let ff ← instantiateMVars falseMVar
  let fMVar ← mkFreshExprMVar $ mkForall "eq" BinderInfo.default (mkConst `False) (← getMVarType mVar)
  assignExprMVar mVar $ mkApp fMVar ff
  let (ffFVar, bodyMVar) ← intro fMVar.mvarId! "eq"
  withMVarContext bodyMVar do
    let _ ← cases bodyMVar ffFVar
    return

def clarifyIndex (mVar : MVarId) (fVar : FVarId) (i : Nat := 0) : MetaM (Option $ FVarSubst × MVarId) :=
  withMVarContext mVar do
    let type ← whnf $ ← inferType $ mkFVar fVar
    let target ← getMVarType mVar
    let failEx := fun _ => throwTacticEx `clarifyIndices mVar "inductive type expected"
    type.withApp fun f args => matchConstInduct f failEx fun val _ => do
      let rhs := args.get! (val.numParams + i)
      unless rhs.isFVar do return (FVarSubst.empty, mVar) --consider failing instead
      let lhs ← mkFreshExprMVar $ ← inferType rhs
      -- First cases run to determine the lhs of the equation
      assignExprMVar lhs.mvarId! $ ← substituteWithCasesOn mVar fVar rhs
      -- Second cases run to actually prove the equality
      let eqType ← mkEq lhs rhs
      let eqMVar ← mkFreshExprMVar eqType
      let eqSubgoals ← cases eqMVar.mvarId! fVar
      if eqSubgoals.size == 0 then
        clarifyIndexFalse mVar fVar i
        return none
      unless eqSubgoals.size == 1 do
        throwTacticEx `clarifyIndices eqMVar.mvarId! "indices must determine constructor uniquely"
      let u ← getLevel (← inferType lhs)
      assignExprMVar eqSubgoals[0].mvarId $ mkApp2 (mkConst `rfl [u]) (← inferType lhs) lhs
      -- Intro the equality as an fVar
      let fMVar ← mkFreshExprMVar $ mkForall "eq" BinderInfo.default eqType target
      assignExprMVar mVar $ mkApp fMVar eqMVar
      let (eqFVar, bodyMVar) ← intro fMVar.mvarId! "eq"
      withMVarContext bodyMVar do
        -- Apply cases on the equality
        let eqCases ← cases bodyMVar eqFVar
        unless eqCases.size == 1 do throwTacticEx `clarifyIndices bodyMVar "could not apply cases on resulting equality"
        let mVar' ← eqCases[0].mvarId
        withMVarContext mVar' do
          let mVar' ← clear mVar' $ Expr.fvarId! $ eqCases[0].subst.apply $ mkFVar eqFVar
          return (eqCases[0].subst, mVar')

def clarifyIndices (mVar : MVarId) (fVar : FVarId) : MetaM (Option $ FVarId × MVarId) :=
  withMVarContext mVar do
    checkNotAssigned mVar `clarifyInstances
    let type ← whnf $ ← inferType $ mkFVar fVar
    let failEx := fun _ => throwTacticEx `clarifyIndices mVar "inductive type expected"
    type.withApp fun f args => matchConstInduct f failEx fun val _ => do
      unless val.numIndices > 0 do throwTacticEx `clarifyIndices mVar "indexed inductive type expected"
      unless args.size == val.numIndices + val.numParams do throwTacticEx `clarifyIndices mVar "ill-formed inductive datatype"
      let mut mVar := mVar
      let mut fVar := fVar
      for i in [:val.numIndices] do
        match ← clarifyIndex mVar fVar i with
        | some  (subst, mVar') => mVar := mVar'
                                  fVar := Expr.fvarId! $ subst.apply $ mkFVar fVar
        | none                 => return none
      return (fVar, mVar)

end Meta

open Tactic

syntax (name := clarifyIndices) "clarifyIndices" (colGt ident)+ : tactic
@[tactic clarifyIndices] def elabClarifyIndices : Tactic
| `(tactic|clarifyIndices $fVars*) => do
  forEachVar fVars fun mVar fVar => do
  match ← Meta.clarifyIndices mVar fVar with
  | some (_, mVar) => return mVar
  | none           => return mVar
| _ => throwUnsupportedSyntax

end Lean


-- Examples
inductive Foo : (n : Nat) → Fin n → Prop
| mk1 : Foo 5 0
| mk2 : Foo 8 3

def bar (x : Fin 5) (p : Foo 5 x) (A : Type) (a : Foo 5 0 → A) : A := by
  clarifyIndices p
  exact a p

def baz (x : Fin 6) (p : Foo 6 x) (A : Type) : A := by
  clarifyIndices p

inductive Foo' : (m n : Nat) → Fin (m + n) → Prop
| mk1 : Foo' 4 2 0
| mk2 : Foo' 1 3 1

def bar' (y : Nat) (x : Fin 6) (p : Foo' 4 2 x) (A : Type) (a : Foo' 4 2 0 → A) : A := by
  clarifyIndices p
  exact a p

inductive Foo'' : (m n l : Nat) → Prop
| mk1 : Foo'' 1 2 3
| mk2 : (x : Nat) → Foo'' 4 x 6

def bar'' (x y : Nat) (p : Foo'' x y 3) (h : x < y) : Foo'' x 2 3 := by
  clarifyIndices p
  exact p

def bar''' (x y : Nat) (p : Foo'' 4 (x + 1) y) : Foo'' 4 (x + 1) 6 := by
  clarifyIndices p
  exact p
