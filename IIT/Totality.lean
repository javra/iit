/- Proves the totality of the eliminator relation -/

import IIT.Relation
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
introMethods mVar ctorIdss (i + 1) (fVarss.push fVars)

inductive HeaderArg where
| internal : FVarId → FVarId → FVarId → HeaderArg
| external : FVarId → HeaderArg
deriving Inhabited

private def HeaderArg.toExpandedExprs (ha : HeaderArg) : Array Expr :=
match ha with
| internal s m r => #[mkFVar s, mkFVar m, mkFVar r]
| external n     => #[mkFVar n]

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

private partial def totalityRecMotiveAux_old (e : Expr) 
  (wref rref : Expr) (mainE : Expr) : MetaM Expr := do
match e with
| forallE n t b _ => 
  match headerAppIdx? its t with
  | some j => mkForallM n e.binderInfo t fun sFVar => do
                let se := mkFst sFVar
                let sw := mkSnd sFVar
                let m := mkApp (← methodTmS its methods motives t t) sFVar
                mkForallM (n ++ motiveSuffix) BinderInfo.default m fun mFVar => do
                  let r := mkAppN (← elimRelationCtorTmS its motives methods t t) #[sFVar, mFVar]
                  mkForallM (n ++ relationSuffix) BinderInfo.default r fun rFVar => do
                    let wref := mkApp wref se
                    let rref := mkAppN rref #[sFVar, mFVar]
                    totalityRecMotiveAux_old b wref rref mainE
  | none   => mkForallM n e.binderInfo t fun extFVar => do
                let wref := mkApp wref extFVar
                let rref := mkApp rref extFVar
                totalityRecMotiveAux_old b wref rref mainE
| sort l _        => let w := mkApp wref mainE
                     mkForallM "mainw" BinderInfo.default w fun mainw => do
                       mkSigmaM $ mkApp rref $ ← mkPair mainE mainw
| _ => e

private partial def totalityRecMotiveAux (e : Expr) 
  (wref rref : Expr) (mainE : Expr) (em er : Expr := e) : MetaM Expr := do
match e with
| forallE n t b _ => do
  match headerAppIdx? its t with
  | some j => (let m := mkApp (← methodTmS its methods motives (liftBVarsOne t) (liftBVarsOne $ bindingDomain! em)) (mkBVar 0)
               let r := mkAppN (← elimRelationCtorTmS its motives methods (liftBVarsTwo t) (liftBVarsTwo $ bindingDomain! er))
                          #[mkBVar 1, mkBVar 0]
	       let wref := mkApp (liftBVarsThree wref) $ mkFst $ mkBVar 2
	       let rref := mkAppN (liftBVarsThree rref) #[mkBVar 2, mkBVar 1]
	       let b'   := liftBVarsTwo b
	       let bm   := liftBVarsOne $ bindingBody! em
	       let br   := bindingBody! er
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

inductive CtorArg where
| internal : FVarId → CtorArg
| external : FVarId → CtorArg
deriving Inhabited

private def CtorArg.toExpr (ca  : CtorArg) : Expr :=
match ca with
| internal fv => mkFVar fv
| external fv => mkFVar fv

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

private partial def hdArgsCases (mVar : MVarId) (hdArgs : Array HeaderArg)
  (fVars : Array (Expr × Expr) := #[]) : TacticM (Array (Expr × Expr) × MVarId) := do
if fVars.size >= hdArgs.size then return (fVars, mVar) else do
  let i := fVars.size
  let lCtx ← getLCtx
  match hdArgs[i] with
  | HeaderArg.internal fVar _ _ => 
    let name := (lCtx.get! fVar).userName
    let (mVar, E, w) ← casesPSigma mVar fVar (name ++ erasureSuffix) (name ++ wellfSuffix)
    hdArgsCases mVar hdArgs $ fVars.push (E, w)
  | HeaderArg.external fVar =>
    hdArgsCases mVar hdArgs $ fVars.push (mkFVar fVar, mkFVar fVar)

private def collectCtorIndicesTmS (e : Expr) (inds : Array Expr := #[]) : Array Expr :=
match e with
| app f e _   => inds.push (wellfCtorTmP its e)
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
    let eqMVar ← casesNoFields eqMVar witness
    withMVarContext eqMVar do
      let gs ← getGoals
      setGoals [eqMVar]
      evalTactic $ ← `(tactic|rfl)
      setGoals gs
  withMVarContext mVar' do
    proveEqs mVar' eqs witness (i + 1) $ eqFVars.push eqFVar

partial def casesEqs (mVar : MVarId) (eqFVars : Array FVarId) (i : Nat := 0) : TacticM MVarId :=
if i >= eqFVars.size then return mVar else do
  let mVar ← casesNoFields mVar eqFVars[i]
  withMVarContext mVar do
    casesEqs mVar eqFVars (i + 1)

def totalityInnerTac (hIdx sIdx ctorIdx : Nat) (its : List InductiveType) (mVar : MVarId) : TacticM MVarId := do
  let it   := its.get! sIdx
  let ctor := it.ctors.get! ctorIdx
  let (ctorArgs, mVar) ← introErasedCtorArgs its mVar ctor.type
  withMVarContext mVar do
    let (ctorIHs, mVar) ← introIHs its mVar ctor.type
    let (hdArgs, mVar) ← introHdArgs its mVar it.type
    withMVarContext mVar do
      let (Ews, mVar) ← hdArgsCases mVar hdArgs
      withMVarContext mVar do
        let (ctorw, mVar) ← intro mVar "ctorw"
        withMVarContext mVar do
          let ctorIndices ← collectCtorIndices its ctor.type
          let ctorIndices := ctorIndices.map fun ci =>
            instantiateRev ci $ ctorArgs.map CtorArg.toExpr
          let eqs ← mkEqs ctorIndices (Ews.map Prod.fst)
          let (eqFVars, mVar) ← proveEqs mVar eqs ctorw
          withMVarContext mVar do
            let mVar ← casesEqs mVar eqFVars
            return mVar

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
  let (mVar, mainE, mainw) ← casesPSigma mVar sMain (sMainName ++ erasureSuffix) (sMainName ++ wellfSuffix)
  withMVarContext mVar do
    let mut recMotives := #[]
    for i in [:its.length] do
      let mot ← totalityRecMotive motives methodss i its
      recMotives := recMotives.push mot
    let recApp := mkAppN (mkConst (mainIT.name ++ erasureSuffix ++ "rec") [levelOne]) recMotives --TODO levels
    let (methodGoals, recApp) ← appExprHoleN methods.size recApp --TODO
    let recApp := mkAppN recApp (#[mainE] ++ (hArgs.map HeaderArg.toExpandedExprs).concat ++ #[mainw])
    assignExprMVar mVar recApp
    let mut i' := 0
    let mut methodGoals := methodGoals.toArray
    for i in [:methodss.size] do
      for j in [:methodss[i].size] do
        methodGoals ← methodGoals.modifyM i' $ fun g => 
          totalityInnerTac hIdx i j its g
        i' := i' + 1
    setGoals methodGoals.toList

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
