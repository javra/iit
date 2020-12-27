/- Construction of the initial IIT algebra -/

import Lean.Elab
import Init.Data.Array.Basic
import IIT.InductiveUtils
import IIT.Erasure
import IIT.Wellformedness

open Lean
open Elab
open Command
open Meta
open Expr
open Array

namespace IIT

variables (its eits wits : List InductiveType)

def resultingLevel (e : Expr) : Level :=
match e with
| forallE n t b d => resultingLevel b
| sort l d        => l
| _ => levelZero

def mkSigma (l : Level) (α β : Expr) : Expr :=
mkApp (mkApp (mkConst `PSigma [l, levelZero]) α) β

def mkFst (l : Level) (x : Expr) : Expr := mkProj `PSigma 0 x

def sigmaHeader (i : Nat) (e : Expr := (its.get! i).type) (wref := mkConst (wits.get! i).name) : Expr :=
match e with
| sort l d        => mkSigma l (mkConst (eits.get! i).name) wref
| forallE n t b d => 
  match headerAppIdx? its t with
  | some j => let jfst := mkFst (resultingLevel $ (its.get! j).type) (mkBVar 0)
              let wref := liftLooseBVars wref 0 1
              let b := sigmaHeader i b (mkApp wref jfst)
              mkLambda n e.binderInfo t b
  | none   => let wref := liftLooseBVars wref 0 1
              let b := sigmaHeader i b (mkApp wref (mkBVar 0))
              mkLambda n e.binderInfo t b
| app f e d       => return mkApp (← sigmaHeader i f) e
| _               => e

partial def sigmaDecls (i : Nat := 0) (decls : List Declaration := []) : TermElabM $ List Declaration :=
if i >= its.length then return decls else
do let hr ← sigmaHeader its eits wits i
   let type := (its.get! i).type
   let decl := Declaration.defnDecl { name     := (its.get! i).name, 
                                      lparams  := [], --TODO
                                      value    := hr
                                      type     := type,
                                      hints    := arbitrary,
                                      isUnsafe := false };
    sigmaDecls (i + 1) (decls.append [decl])

end IIT
