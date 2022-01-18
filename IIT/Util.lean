/- General purpose utility functions -/
import Lean.Expr
import Lean.Elab
open Lean
open Elab
open Meta

namespace Lean

namespace Expr

def liftBVarsOne (e : Expr) : Expr := liftLooseBVars e 0 1

def liftBVarsTwo (e : Expr) : Expr := liftLooseBVars e 0 2

def liftBVarsThree (e : Expr) : Expr := liftLooseBVars e 0 3

def resultingLevel (e : Expr) : Level :=
match e with
| forallE n t b d => resultingLevel b
| sort l d        => l
| _ => levelZero

def mkForallM (n : Name) (bi : BinderInfo) (t : Expr) (b : Expr → MetaM Expr) : MetaM Expr := do
withLocalDecl n bi t $ fun fVar => do
  mkForallFVars #[fVar] $ instantiate1 (← b fVar) fVar

def mkLambdaM (n : Name) (bi : BinderInfo) (t : Expr) (b : Expr → MetaM Expr) : MetaM Expr := do
withLocalDecl n bi t $ fun fVar => do
  mkLambdaFVars #[fVar] $ instantiate1 (← b fVar) fVar

def mkSigma (l : Level) (α β : Expr) : Expr :=
mkApp (mkApp (mkConst `PSigma [l, levelZero]) α) β

def mkSigmaM (β : Expr) : MetaM Expr := mkAppM `PSigma #[β]

def mkFst (x : Expr) : Expr := mkProj `PSigma 0 x

def mkSnd (x : Expr) : Expr := mkProj `PSigma 1 x

def mkPair (p q : Expr) : MetaM Expr := mkAppM `PSigma.mk #[p, q]

end Expr

namespace Meta

def appExprHole (f : Expr) : MetaM (MVarId × Expr) := do
  let t ← inferType f
  match t with
  | Expr.forallE _ t _ _ =>
    let mVar ← mkFreshExprMVar t
    return (mVar.mvarId!, mkApp f mVar)
  | _ => throwError "can only apply 'appExprHole' on pi types"

partial def appExprHoleN (n : Nat) (f : Expr) : MetaM (List MVarId × Expr) :=
if n = 0 then return ([], f) else do
  let (mids, f) ← appExprHoleN (n - 1) f
  let (mid, f) ← appExprHole f
  return (mids.append [mid], f)

def FVarSubst.append (s1 s2 : FVarSubst) : FVarSubst :=
let f s k v := (s.erase k).insert k $ s.apply v
s1.map.foldl f s2

open Tactic

instance : Inhabited CasesSubgoal := Inhabited.mk $ CasesSubgoal.mk default ""

def casesPSigma (mVar : MVarId) (fVar : FVarId) (fstName sndName : Name) :
  MetaM (FVarId × FVarId × MVarId) := do
  let sgs ← cases mVar fVar --#[[fstName, sndName]] TODO names?
  return (sgs[0].fields[0].fvarId!, sgs[0].fields[1].fvarId!, sgs[0].mvarId)

def casesNoFields (mVar : MVarId) (fVar : FVarId) : TacticM (FVarSubst × MVarId) := do
  let sgs ← cases mVar fVar --#[[]]
  return (sgs[0].subst, sgs[0].mvarId)

partial def withLocalDeclDs {α} (names : Array Name) (vals : Array Expr) 
  (x : Array FVarId → MetaM α) (fVars : Array FVarId := #[]) : MetaM α :=
let i := fVars.size
if i >= vals.size then x fVars else do
  withLocalDeclD names[i] vals[i] fun fVar => do
    withLocalDeclDs names vals x $ fVars.push fVar.fvarId!

/- Performs a Tactic akin to "have" and returns
   1. the MVar for the auxiliary proof goal,
   2. the MVar to continue working using a proof of the auxiliary statement, including a FVarId to ref it,
   3. the expression to be assigned to the original proof goal to make it all work out. -/
def metaHave (mVar : MVarId) (name : Name) (type : Expr) : MetaM (MVarId × (FVarId × MVarId) × Expr) := do
  let val ← mkFreshExprMVar type
  let valMVar := val.mvarId!
  let bodyType ← getMVarType mVar
  let f ← mkFreshExprMVar $ mkForall name BinderInfo.default type bodyType
  let fMVar := f.mvarId!
  let bodyMVar ← intro fMVar name
  return (valMVar, bodyMVar, mkApp f val)

end Meta

end Lean

namespace Array

def concat {α} (xss : Array (Array α)) : Array α := Array.foldl Array.append #[] xss

end Array
