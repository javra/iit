/- Eliminator relation -/

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

variables (its : List InductiveType) (ls : List Level)

def motiveSuffix : Name := "m"

def motive (l : Level) (fVars : Array Expr) (e : Expr) (ref : Expr) : Expr :=
match e with
| forallE n t b d =>
   match headerAppIdx? its t with
  | some j => mkForall n BinderInfo.implicit (mkConst (its.get! j).name) $
              mkForall (n ++ "m") e.binderInfo (mkApp fVars[j] $ mkBVar 0) $ -- ??
              motive l fVars b (mkApp (liftLooseBVars ref 0 2) (mkBVar 0))
  | none   => mkForall n e.binderInfo t $
              motive l fVars b (mkApp (liftLooseBVars ref 0 1) (mkBVar 0))
| sort l' d       => mkForall "x" BinderInfo.default ref (mkSort l) --TODO name
| _ => e

partial def withMotives {α} (x : Array Expr → TermElabM α)
  (i : Nat := 0) (fVars : Array Expr := #[]) : TermElabM α :=
if i >= its.length then x fVars else
let name := (its.get! i).name ++ motiveSuffix
let type := motive its (ls.get! i) fVars (its.get! i).type (mkConst (its.get! i).name)
withLocalDeclD name type fun fVar => do
  withMotives x (i + 1) (fVars.push fVar)


end IIT