/- Construction of the initial IIT algebra -/

import Init.Data.Array.Basic
import IIT.Wellformedness
import IIT.Util

open Lean
open Elab
open Command
open Meta
open Lean.Expr
open Array

namespace IIT

variable (its eits wits : List InductiveType)

def sigmaHeader (i : Nat) (e : Expr := (its.get! i).type) (wref := mkConst (wits.get! i).name) : Expr :=
match e with
| sort l _        => mkSigma l (mkConst (eits.get! i).name) wref
| forallE n t b _ => 
  match headerAppIdx? its t with
  | some _ => let jfst := mkFst $ mkBVar 0
              let wref := liftBVarsOne wref
              mkLambda n e.binderInfo t $ sigmaHeader i b (mkApp wref jfst)
  | none   => let wref := liftBVarsOne wref
              mkLambda n e.binderInfo t $ sigmaHeader i b (mkApp wref (mkBVar 0))
| app f e _       => mkApp (sigmaHeader i f) e
| _               => e

def sigmaCtorTmS (e : Expr) (eref wref : Expr) : TermElabM Expr := do
match e with
| app f _ _   => sigmaCtorTmS f eref wref
| const _ _ _ => mkPair eref wref
| _           => return e

def sigmaCtor (ctorName : Name) (e : Expr)
 (eref : Expr := mkConst $ ctorName ++ erasureSuffix)
 (wref : Expr := mkConst $ ctorName ++ wellfSuffix) : TermElabM Expr := do
match e with
| forallE n t b _ =>
  match headerAppIdx? its t with
  | some _ => let eref := mkApp (liftBVarsOne eref) $ mkFst $ mkBVar 0
              let wref := mkApp (mkApp (liftLooseBVars wref 0 1) (mkFst (mkBVar 0))) (mkSnd (mkBVar 0))
              return mkLambda n e.binderInfo t $
               ← sigmaCtor ctorName b eref wref
  | none   => let eref := mkApp (liftBVarsOne eref) (mkBVar 0)
              let wref := mkApp (liftBVarsOne wref) (mkBVar 0)
              return mkLambda n e.binderInfo t $
              ← sigmaCtor ctorName b eref wref
| _ => sigmaCtorTmS e eref wref --"El" Case

partial def sigmaDecls (i : Nat := 0) (hDecls ctorDecls : List Declaration := []) :
 TermElabM $ List Declaration :=
if i >= its.length then return hDecls ++ ctorDecls else do
  let hr := sigmaHeader its eits wits i
  let it := its.get! i
  let type := it.type
  let ctors ← it.ctors.mapM fun ctor => do
    let sctor ← sigmaCtor its ctor.name ctor.type
    return Declaration.defnDecl { name := ctor.name,
                                  levelParams := [], --TODO
                                  value := sctor,
                                  type := ctor.type,
                                  hints := ReducibilityHints.regular 0,
                                  safety := DefinitionSafety.safe }
  let decl := Declaration.defnDecl { name     := (its.get! i).name, 
                                     levelParams  := [], --TODO
                                     value    := hr
                                     type     := type,
                                     hints    := default,
                                     safety   := DefinitionSafety.safe }
  sigmaDecls (i + 1) (hDecls ++ [decl]) (ctorDecls ++ ctors)

end IIT
