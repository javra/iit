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

variables (its : List InductiveType) (ls : List Level)
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
                                   lparams  := [], -- TODO
                                   value    := tot,
                                   type     := type,
                                   hints    := arbitrary -- TODO
                                   safety   := DefinitionSafety.safe }
totalityTypes (i + 1) (decls.append [decl])

open Lean.Parser
open Lean.Elab.Command
open Lean.Elab.Term

partial def introMethods (mVar : MVarId) (ctorIdss : List (List Name)) (i : Nat := 0) (fVarss : Array (Array FVarId) := #[]) :
  MetaM (Array (Array FVarId) × MVarId) :=
if i >= ctorIdss.length then return (fVarss, mVar) else do
let (fVars, mVar) ← introN mVar (ctorIdss.get! i).length ((ctorIdss.get! i).map fun n => n ++ "m")
introMethods mVar ctorIdss (i + 1) (fVarss.push fVars)

partial def introHdArgs (mVar : MVarId) (hdType : Expr) (fVars : Array FVarId := #[]) :
  MetaM (Array FVarId × MVarId) := do --TODO swap FVarId for annotated child type
match hdType with
| forallE n t b _ =>
  match headerAppIdx? its t with
  | some j => let (fVars', mVar) ← introN mVar 3 [n, n ++ motiveSuffix, n ++ relationSuffix]
              introHdArgs mVar b (fVars.append fVars')
  | none   => let (fVar, mVar) ← intro mVar n
              introHdArgs mVar b (fVars.push fVar)
| _ => return (fVars, mVar)

def totalityOuterTac (hIdx : Nat) (its : List InductiveType) : TacticM Unit :=
liftMetaTactic fun mainMVar => do
  let hType ← inferType $ mkConst (its.get! hIdx).name --TODO levels?
  let (motives, mainMVar) ← introN mainMVar its.length (its.map fun it => it.name ++ "m")
  let (methods, mainMVar) ← introMethods mainMVar (its.map fun it => it.ctors.map fun ctor => ctor.name)
  let (hArgs,   mainMVar) ← introHdArgs its mainMVar hType -- TODO intro hd args
  let (sMain, mainMVar) ← intro mainMVar "sMain"
  return [mainMVar]

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
