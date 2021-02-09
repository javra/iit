/- Proves the totality of the eliminator relation -/

import IIT.Relation
import IIT.ClarifyIndices
import Lean.Elab.Tactic

open Lean
open Elab
open Command
open Meta
open Expr
open Array
open Tactic

namespace IIT

variable (its : List InductiveType) (ls : List Level)
  (motives : Array Expr) (methods : Array (Array Expr))

partial def totalityType (l : Level) (e sref dref rref : Expr) : MetaM Expr := do
match e with
| forallE n t b _ => 
  match headerAppIdx? its t with
  | some _ => let t' := liftBVarsOne t
              let tm := mkApp (motiveAux its motives t' t) $ mkBVar 0
              let tr ← elimRelationCtorTmS its motives methods (liftBVarsTwo t) t'
              let tr := mkApp (mkApp tr $ mkBVar 1) $ mkBVar 0
              let sref := mkApp (liftBVarsThree sref) $ mkBVar 2
              let dref := mkApp (mkApp (liftBVarsThree dref) $ mkBVar 2) $ mkBVar 1
              let rref := mkApp (mkApp (liftBVarsThree rref) $ mkBVar 2) $ mkBVar 1
              mkForall n e.binderInfo t $
              mkForall (n ++ motiveSuffix) BinderInfo.implicit tm $
              mkForall (n ++ relationSuffix) BinderInfo.default tr $
              ← totalityType l (liftBVarsTwo b) sref dref rref
  | none   => let sref := mkApp (liftBVarsOne sref) $ mkBVar 0
              let dref := mkApp (liftBVarsOne dref) $ mkBVar 0
              let rref := mkApp (liftBVarsOne rref) $ mkBVar 0
              mkForall n e.binderInfo t $
              ← totalityType l b sref dref rref
| sort l _  => let dref := liftBVarsOne dref
               let rref := liftBVarsOne rref
               mkForall "s" BinderInfo.default sref $
               mkSigma l (mkApp dref $ mkBVar 0) (mkApp rref $ mkBVar 0)
| _ => e

partial def totalityTypes (i : Nat := 0) (decls : List Declaration := []) : MetaM $ List Declaration :=
if i >= its.length then decls else do
let name := (its.get! i).name
let type := (its.get! i).type
let rref := mkAppN (mkConst $ name ++ relationSuffix) (motives ++ methods.concat)
let tot ← totalityType its motives methods (ls.get! i) type (mkConst name) motives[i] rref --TODO level
let tot ← mkForallFVars (motives ++ methods.concat) tot
let type ← inferType tot
let decl := Declaration.defnDecl { name     := name ++ "tot",
                                   levelParams  := [], -- TODO
                                   value    := tot,
                                   type     := type,
                                   hints    := arbitrary -- TODO
                                   safety   := DefinitionSafety.safe }
totalityTypes (i + 1) (decls.append [decl])

open Lean.Parser
open Lean.Elab.Command
open Lean.Elab.Term

private partial def introMethods (mVar : MVarId) (ctorIdss : List (List Name)) (i : Nat := 0) (fVarss : Array (Array FVarId) := #[]) :
  MetaM (Array (Array FVarId) × MVarId) :=
if i >= ctorIdss.length then return (fVarss, mVar) else do
let (fVars, mVar) ← introN mVar (ctorIdss.get! i).length ((ctorIdss.get! i).map fun n => n ++ "m")
introMethods mVar ctorIdss (i + 1) (fVarss.push fVars
)
def foo (e : Expr) : MetaM Expr := do
match e with
| forallE n t b _ => let m ← mkPair t b
                     return m
| _ => e

private partial def totalityRecMotiveAux (e : Expr) 
  (wref rref : Expr) (mainE : Expr) (em er : Expr := e) : MetaM Expr := do
match e with
| forallE n t b _ =>
  match headerAppIdx? its t with
  | some j => (let m := mkApp (← methodTmS its methods motives (liftBVarsOne t) (liftBVarsOne $ bindingDomain! em)) (mkBVar 0)
               let r := mkAppN (← elimRelationCtorTmS its motives methods (liftBVarsTwo t) (liftBVarsTwo $ bindingDomain! er))
                          #[mkBVar 1, mkBVar 0]
	       let wref := mkApp (liftBVarsThree wref) $ mkFst $ mkBVar 2
	       let rref := mkAppN (liftBVarsThree rref) #[mkBVar 2, mkBVar 1]
	       let b'   := liftBVarsTwo b
	       let bm   := liftBVarsOne $ bindingBody! em
	       let br   := liftBVarsOne $ bindingBody! er --????
               return mkForall n e.binderInfo t $
                 mkForall (n ++ motiveSuffix) BinderInfo.default m $
	         mkForall (n ++ relationSuffix) BinderInfo.default r $
	         ← totalityRecMotiveAux b' wref rref mainE bm br)
  | none => let wref := mkApp (liftBVarsOne wref) (mkBVar 0)
            let rref := mkApp (liftBVarsOne wref) (mkBVar 0)
            let bm   := bindingBody! em
            let br   := bindingBody! er
            mkForall n e.binderInfo t $
             ← totalityRecMotiveAux b wref rref mainE bm br
| _ => let w := mkApp wref mainE
       mkForallM "mainw" BinderInfo.default w fun mainw => do
         mkSigmaM $ liftBVarsTwo $ mkApp rref $ ← mkPair mainE mainw --????

private def totalityRecMotive (hIdx : Nat) (its : List InductiveType) : MetaM Expr :=
let name := (its.get! hIdx).name
let type := (its.get! hIdx).type
let rref := mkAppN (mkConst (name ++ relationSuffix)) (motives ++ methods.concat)
mkLambdaM "mainE" BinderInfo.default (mkConst $ name ++ erasureSuffix) fun EFVar =>
  totalityRecMotiveAux its motives methods (its.get! hIdx).type (mkConst $ name ++ wellfSuffix) rref EFVar

def sMainName : Name := "S"

inductive HeaderArg where
| internal : FVarId → FVarId → FVarId → HeaderArg
| external : FVarId → HeaderArg
deriving Inhabited

private def HeaderArg.toExpandedExprs (ha : HeaderArg) : Array Expr :=
match ha with
| internal s m r => #[mkFVar s, mkFVar m, mkFVar r]
| external n     => #[mkFVar n]

inductive HeaderArg' where
| internal : FVarId → FVarId → FVarId → FVarId → HeaderArg'
| external : FVarId → HeaderArg'
deriving Inhabited

private def HeaderArg'.toErasureOrExt (ha : HeaderArg') : Expr :=
match ha with
| internal e _ _ _ => mkFVar e
| external n       => mkFVar n

private partial def HeaderArg'.toRelationArray (has : Array HeaderArg')
  (i : Nat := 0) (fVars : Array FVarId := #[]) : Array FVarId :=
if i >= has.size then return fVars else do
  match has[i] with
  | internal _ _ _ r => return toRelationArray has (i + 1) $ fVars.push r
  | _                => return toRelationArray has (i + 1) fVars

inductive CtorArg where
| internal : FVarId → CtorArg
| external : FVarId → CtorArg
deriving Inhabited

private def CtorArg.toExpr (ca  : CtorArg) : Expr :=
match ca with
| internal fv => mkFVar fv
| external fv => mkFVar fv

private partial def introHdArgs (mVar : MVarId) (hdType : Expr) (has : Array HeaderArg := #[]) :
  MetaM (Array HeaderArg × MVarId) := do
match hdType with
| forallE n t b _ =>
  match headerAppIdx? its t with
  | some _ => let (fVars', mVar) ← introN mVar 3 [n, n ++ motiveSuffix, n ++ relationSuffix]
              let ha := HeaderArg.internal fVars'[0] fVars'[1] fVars'[2]
              introHdArgs mVar b (has.push ha)
  | none   => let (fVar, mVar) ← intro mVar n
              introHdArgs mVar b (has.push $ HeaderArg.external fVar)
| _ => return (has, mVar)

private partial def introCasesHdArgs (mVar : MVarId) (hdType : Expr) (has : Array HeaderArg' := #[]) :
  MetaM (Array HeaderArg' × MVarId) := do
match hdType with
| forallE n t b _ =>
  match headerAppIdx? its t with
  | some _ => let (sfVar, mVar) ← intro mVar n
              let (EfVar, wfVar, mVar) ← casesPSigma mVar sfVar (n ++ erasureSuffix) (n ++ wellfSuffix)
              let (fVars', mVar) ← introN mVar 2 [n ++ motiveSuffix, n ++ relationSuffix]
              let ha := HeaderArg'.internal EfVar wfVar fVars'[0] fVars'[1]
              introCasesHdArgs mVar b (has.push ha)
  | none   => let (fVar, mVar) ← intro mVar n
              introCasesHdArgs mVar b (has.push $ HeaderArg'.external fVar)
| _ => return (has, mVar)

private partial def introErasedCtorArgs (mVar : MVarId) (ctorType : Expr) (cas : Array CtorArg := #[]) :
  MetaM (Array CtorArg × MVarId) := do
match ctorType with
| forallE n t b _ =>
  match headerAppIdx? its t with
  | some _ => let (fVar, mVar) ← intro mVar (n ++ erasureSuffix)
              introErasedCtorArgs mVar b $ cas.push $ CtorArg.internal fVar
  | none   => let (fVar, mVar) ← intro mVar n
              introErasedCtorArgs mVar b $ cas.push $ CtorArg.external fVar
| _ => return (cas, mVar)

def ihSuffix : Name := "ih"

private partial def introIHs (mVar : MVarId) (ctorType : Expr) (fVars : Array FVarId := #[]) :
  MetaM (Array FVarId × MVarId) := do
match ctorType with
| forallE n t b _ =>
  match headerAppIdx? its t with
  | some _ => let (fVar, mVar) ← intro mVar (n ++ ihSuffix)
              introIHs mVar b $ fVars.push fVar
  | none   => introIHs mVar b $ fVars
| _ => return (fVars, mVar)

private def collectCtorIndicesTmS (e : Expr) (inds : Array Expr := #[]) : Array Expr := do
match e with
| app f e _   => let inds ← collectCtorIndicesTmS f inds
                 inds.push (wellfCtorTmP its e)
| _           => inds

private def collectCtorIndices (e : Expr) : MetaM (Array Expr) := --TODO replace this by a simple call to some Expr def
match e with
| forallE _ _ b _ => collectCtorIndices b
| _ => collectCtorIndicesTmS its e

private partial def mkEqs (lhs rhs : Array Expr) : MetaM (Array Expr) := do
  let lr := Array.zip lhs rhs
  lr.mapM $ fun (lh, rh) => mkEq lh rh

partial def proveEqs (mVar : MVarId) (eqs : Array Expr) (witness : FVarId) (i : Nat := 0)
  (eqFVars : Array FVarId := #[]) :  TacticM (Array FVarId × MVarId) :=
if i >= eqs.size then return (eqFVars, mVar) else do
  let (eqMVar, (eqFVar, mVar'), mVarSolution) ← metaHave mVar "e''" eqs[i]
  assignExprMVar mVar mVarSolution
  withMVarContext eqMVar do
    let (_, eqMVar) ← casesNoFields eqMVar witness
    withMVarContext eqMVar do
      let gs ← getGoals
      setGoals [eqMVar]
      evalTactic $ ← `(tactic|rfl)
      setGoals gs
  withMVarContext mVar' do
    proveEqs mVar' eqs witness (i + 1) $ eqFVars.push eqFVar

partial def casesEqs (mVar : MVarId) (subst : FVarSubst) (eqFVars : Array FVarId) (i : Nat := 0)
  : TacticM (FVarSubst × MVarId) :=
if i >= eqFVars.size then return (subst, mVar) else do
  let (subst', mVar) ← casesNoFields mVar eqFVars[i]
  withMVarContext mVar do
    casesEqs mVar (subst.append subst') eqFVars (i + 1)

def totalityModelTac (hdArgs : Array HeaderArg') (subst : FVarSubst) (mVar : MVarId) :
   TacticM (FVarSubst × MVarId) :=
withMVarContext mVar do
  setGoals [mVar]
  let rFVars := HeaderArg'.toRelationArray hdArgs
  let mut mVar := mVar
  let mut subst := subst
  for rFVar in rFVars do
    let foo ← try (clarifyIndicesTac mVar (subst.get rFVar).fvarId!) catch _ => pure none
    match foo with
    | none => return (subst, mVar)
    | some (s, mVar') => do
      subst := subst.append s
      mVar  := mVar'
  return (subst, mVar)

def totalityInnerTac (hIdx sIdx ctorIdx : Nat) (its : List InductiveType) (mVar : MVarId) :
  TacticM (Array MVarId) := do
  let it       := its.get! sIdx
  let ctor     := it.ctors.get! ctorIdx
  let accSubst := FVarSubst.empty
  let (ctorArgs, mVar) ← introErasedCtorArgs its mVar ctor.type
  withMVarContext mVar do
    let (ctorIHs, mVar) ← introIHs its mVar ctor.type
    let (hdArgs, mVar) ← introCasesHdArgs its mVar it.type
    withMVarContext mVar do
      let (ctorw, mVar) ← intro mVar "ctorw"
      withMVarContext mVar do
        let ctorIndices ← collectCtorIndices its ctor.type
        let ctorIndices := ctorIndices.map fun ci =>
          instantiateRev ci $ ctorArgs.map CtorArg.toExpr
        let eqs ← mkEqs ctorIndices $ hdArgs.map HeaderArg'.toErasureOrExt
        let (eqFVars, mVar) ← proveEqs mVar eqs ctorw
        withMVarContext mVar do
          let (accSubst, mVar) ← casesEqs mVar accSubst eqFVars
          withMVarContext mVar do
            let type ← getMVarType mVar
            setGoals [mVar]
            let (resPair, mVars) ← elabTermWithHoles (Unhygienic.run `(PSigma.mk ?_ ?_)) type "foo"
            assignExprMVar mVar resPair
            setGoals [mVars.get! 0]
            let (accSubst, mmVar) ← totalityModelTac hdArgs accSubst $ mVars.get! 0
            let rmVar := mVars.get! 1
            return #[mmVar, rmVar]

def totalityOuterTac (hIdx : Nat) (its : List InductiveType) : TacticM Unit := do
  let mainIT := its.get! hIdx
  let (mVar, _) ← getMainGoal
  let hType ← inferType $ mkConst mainIT.name --TODO levels?
  let (motives, mVar) ← introN mVar its.length (its.map fun it => it.name ++ "m")
  let (methodss, mVar) ← introMethods mVar (its.map fun it => it.ctors.map fun ctor => ctor.name)
  let motives  := motives.map mkFVar
  let methodss := methodss.map fun ms => ms.map mkFVar
  let methods := methodss.concat
  let (hArgs,   mVar) ← introHdArgs its mVar hType
  let (sMain,   mVar) ← intro mVar sMainName
  let (mainE, mainw, mVar) ← casesPSigma mVar sMain (sMainName ++ erasureSuffix) (sMainName ++ wellfSuffix)
  withMVarContext mVar do
    let mut recMotives := #[]
    for i in [:its.length] do
      let mot ← totalityRecMotive motives methodss i its
      recMotives := recMotives.push mot
    let recApp := mkAppN (mkConst (mainIT.name ++ erasureSuffix ++ "rec") [levelOne]) recMotives --TODO levels
    let (methodGoals, recApp) ← appExprHoleN methods.size recApp --TODO
    let recApp := mkAppN recApp (#[mkFVar mainE] ++ (hArgs.map HeaderArg.toExpandedExprs).concat 
                                                 ++ #[mkFVar mainw])
    assignExprMVar mVar recApp
    let mut methodGoalss : Array (Array MVarId) := #[]
    for i in [:methodss.size] do
      for j in [:methodss[i].size] do
        let gs ← totalityInnerTac hIdx i j its $ methodGoals.get! methodGoalss.size
        methodGoalss := methodGoalss.push gs
    setGoals methodGoalss.concat.toList

instance : Inhabited (Syntax.SepArray ",") := Inhabited.mk $ Syntax.SepArray.ofElems #[]

syntax idList := "[" ident,+,? "]"
syntax (name := totalityOuter) "totalityOuter" num idList+ : tactic
@[tactic totalityOuter] def elabTotalityOuter : Tactic
  | `(tactic|totalityOuter $i $[[$idss,*]]*) => do
    let i := Syntax.toNat i
    let hIds := idss[0].getElems.map Syntax.getId
    let ctorIdss := idss[1:]
    let ctorIdss := ctorIdss.toArray.map fun ctors => ctors.getElems.map Syntax.getId
    let hTypes := hIds.mapM fun hId => inferType $ mkConst hId
    let (its : List InductiveType) ← (List.zip hIds.toList ctorIdss.toList).mapM fun (hId, ctorIds) => do
      let hType ← inferType $ mkConst hId
      let ctors ← ctorIds.mapM λ ctorId => do
        let ctorType ← inferType $ mkConst ctorId
        return { name := ctorId, type := ctorType }
      return { name := hId, type := hType, ctors := ctors.toList : InductiveType } --TODO
    totalityOuterTac i its
  | _  => throwUnsupportedSyntax


end IIT
