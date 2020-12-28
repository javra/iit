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

def mkFst (x : Expr) : Expr := mkProj `PSigma 0 x

def mkSnd (x : Expr) : Expr := mkProj `PSigma 1 x

def mkPair (p q : Expr) : TermElabM Expr := mkAppM `PSigma.mk #[p, q]

def sigmaHeader (i : Nat) (e : Expr := (its.get! i).type) (wref := mkConst (wits.get! i).name) : Expr :=
match e with
| sort l d        => mkSigma l (mkConst (eits.get! i).name) wref
| forallE n t b d => 
  match headerAppIdx? its t with
  | some j => let jfst := mkFst (mkBVar 0)
              let wref := liftLooseBVars wref 0 1
              mkLambda n e.binderInfo t $ sigmaHeader i b (mkApp wref jfst)
  | none   => let wref := liftLooseBVars wref 0 1
              mkLambda n e.binderInfo t $ sigmaHeader i b (mkApp wref (mkBVar 0))
| app f e d       => return mkApp (← sigmaHeader i f) e
| _               => e

def sigmaCtorTmS (e : Expr) (eref wref : Expr) : TermElabM Expr := do
match e with
| app f e d   => sigmaCtorTmS f eref wref
| const n l d => mkPair eref wref
| _           => e

--sigmaCtor _ e should have type e
def sigmaCtor (ctorName : Name) (e : Expr)
 (eref : Expr := mkConst $ ctorName ++ erasureSuffix)
 (wref : Expr := mkConst $ ctorName ++ wellfSuffix) : TermElabM Expr := do
match e with
| forallE n t b d =>
  match headerAppIdx? its t with
  | some j => let eref := mkApp (liftLooseBVars eref 0 1) (mkFst (mkBVar 0))
              let wref := mkApp (mkApp (liftLooseBVars wref 0 1) (mkFst (mkBVar 0))) (mkSnd (mkBVar 0))
              return mkLambda n e.binderInfo t $ ← sigmaCtor ctorName b eref wref
  | none   => let eref := mkApp (liftLooseBVars eref 0 1) (mkBVar 0)
              let wref := mkApp (liftLooseBVars wref 0 1) (mkBVar 0)
              return mkLambda n e.binderInfo t $ ← sigmaCtor ctorName b eref wref
| _ => sigmaCtorTmS e eref wref --"El" Case TODO mkpair goes here

partial def sigmaDecls (i : Nat := 0) (hDecls ctorDecls : List Declaration := []) : TermElabM $ List Declaration :=
if i >= its.length then return hDecls ++ ctorDecls else
do let hr ← sigmaHeader its eits wits i
   let it := its.get! i
   let type := it.type
   let ctors ← it.ctors.mapM fun ctor => do
     let sctor ← sigmaCtor its ctor.name ctor.type
     return Declaration.defnDecl { name := ctor.name,
                                   lparams := [], --TODO
                                   value := sctor,
                                   type := ctor.type,
                                   hints := arbitrary, --TODO set to opaque
                                   isUnsafe := false }
   let decl := Declaration.defnDecl { name     := (its.get! i).name, 
                                      lparams  := [], --TODO
                                      value    := hr
                                      type     := type,
                                      hints    := arbitrary,
                                      isUnsafe := false };
    sigmaDecls (i + 1) (hDecls ++ [decl]) (ctorDecls ++ ctors)

end IIT
