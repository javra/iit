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
def methodSuffix : Name := "m"

def motiveAux (t : Expr) (terminal : Expr) :=
match t with
| app f e d => mkApp (motiveAux f terminal) e
| _         => terminal

partial def motive (l : Level) (fVars : Array Expr) (e : Expr) (ref : Expr) : Expr :=
match e with
| forallE n t b d =>
   match headerAppIdx? its t with
  | some j => let b := liftLooseBVars b 0 1
              --let t' := liftLooseBVars t 0 1
              mkForall n BinderInfo.implicit t $
              mkForall (n ++ "m") e.binderInfo (mkApp (motiveAux t fVars[j]) $ mkBVar 0) $ -- ??
              motive l fVars b (mkApp (liftLooseBVars ref 0 2) (mkBVar 1))
  | none   => mkForall n e.binderInfo t $
              motive l fVars b (mkApp (liftLooseBVars ref 0 1) (mkBVar 0))
| sort l' d       => mkForall "x" BinderInfo.default ref (mkSort l) --TODO name
| _ => e

section
variables (motives : Array Expr)

def methodTmS (e : Expr) : MetaM Expr :=
match e with
| app f e d => mkAppM (methodTmS f) e
| const n l d =>
  match headerAppIdx? its e with
  | some j => motives[j]
  | none   => e
| _ => e

partial def method (name : Name) (e : Expr) (ref := mkConst name) : Expr :=
match e with
| forallE n t b d =>
  match headerAppIdx? its t with
  | some j => let ref := mkApp (liftLooseBVars ref 0 2) $ mkBVar 1
              let t' := liftLooseBVars t 0 1
              let b' := liftLooseBVars b 0 1
              mkForall n BinderInfo.implicit t $
              mkForall (n ++ "m") e.binderInfo 
                (mkApp (methodTmS its motives t) $ mkBVar 0) $
              method name b' ref
  | none   => let ref := mkApp (liftLooseBVars ref 0 1) $ mkBVar 0
              mkForall n e.binderInfo t $
              method name b ref
| _ => mkApp (methodTmS its motives e) ref

end

--TODO generalize the construction of this sort of function
partial def withMotives {α} (x : Array Expr → TermElabM α)
  (i : Nat := 0) (fVars : Array Expr := #[]) : TermElabM α :=
if i >= its.length then x fVars else
let name := (its.get! i).name ++ motiveSuffix
let type := motive its (ls.get! i) fVars (its.get! i).type (mkConst (its.get! i).name)
withLocalDeclD name type fun fVar => do
  withMotives x (i + 1) (fVars.push fVar)

partial def withMethodsAux {α} (motives : Array Expr) (x : Array Expr → TermElabM α)
  (i j : Nat := 0) (fVars : Array Expr := #[]) : TermElabM α :=
if j >= (its.get! i).ctors.length then x fVars else
let ctor := (its.get! i).ctors.get! j
let type := method its motives ctor.name ctor.type
let name := ctor.name ++ methodSuffix
withLocalDeclD name type fun fVar => do
  withMethodsAux motives x i (j + 1) (fVars.push fVar)

partial def withMethods {α} (motives : Array Expr) (x : Array (Array Expr) → TermElabM α)
  (i : Nat := 0) (methods : Array (Array Expr) := #[]) : TermElabM α :=
if i >= its.length then x methods else
withMethodsAux its motives fun fVars =>
  withMethods motives x (i + 1) (methods.push fVars)

def withRecArgs {α} (x : Array Expr → Array (Array Expr) → TermElabM α) : TermElabM α :=
withMotives its ls fun motives =>
  withMethods its motives fun methods =>
    x motives methods

end IIT
