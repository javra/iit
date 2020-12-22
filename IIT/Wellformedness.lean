/- Wellformedness Predicate for IITs -/

import Lean.Elab
import Init.Data.Array.Basic
import IIT.InductiveUtils
import IIT.Erasure

open Lean
open Elab
open Command
open Meta
open Expr
open Array

namespace IIT

def wellfSuffix : String := "w"

section

variables (its eits : List InductiveType)

def headerAppIdx? (e : Expr) : Option Nat :=
match e with
| const n l d => getIdx? (collectHeaderNames its) n
| app f e d   => headerAppIdx? f
| _           => none

def wellfHeader (i : Nat) (e : Expr := (its.get! i).type) : Expr :=
match e with
| sort _ _        => mkForall "e" BinderInfo.default (mkConst $ (eits.get! i).name) (mkSort levelZero)
| forallE n t b d => 
  match headerAppIdx? its t with
  | some j => mkForall n e.binderInfo (mkConst $ (eits.get! j).name) (wellfHeader i b)
  | none   => mkForall n e.binderInfo t (wellfHeader i b)
| lam n t b d     => mkLambda n e.binderInfo (wellfHeader i t) (wellfHeader i b) --TODO not sure if unreachable
| app f e d       => mkApp (wellfHeader i f) e
| _ => e

def addWIfHeader (n : Name) (ct : Name) (l : List Level) : Expr :=
if contains (collectHeaderNames its) n then mkConst (n ++ wellfSuffix) l
else mkConst n l

def wellfCtorTm (i : Nat) (name : Name) (e : Expr) : Expr :=
match e with
| app f e d =>
  match headerAppIdx? its e with -- TODO not e but the _type_ of e
  | some j => mkApp (wellfCtorTm i name f) (wellfCtorTm i name f) --TODO change
  | none   => mkApp (wellfCtorTm i name f) e
| const n l d => addWIfHeader its n name l
| _ => e

def wellfCtor (i : Nat) (name : Name) (e : Expr) (eref : Expr := mkConst (name ++ erasureSuffix)) : Expr :=
match e with
| forallE n t b d =>
  match headerAppIdx? its t with
  | some j => mkForall (n ++ "e") BinderInfo.default (mkConst $ (eits.get! j).name) $
                mkForall (n ++ "w") b.binderInfo (mkApp (mkConst $ (its.get! j).name ++ wellfSuffix) (mkBVar 0)) $
                  wellfCtor i name b (mkApp eref (mkBVar 1))
  | none   => mkForall n e.binderInfo t $ 
                wellfCtor i name b (mkApp eref (mkBVar 0))
| _ => mkApp (wellfCtorTm its i name e) eref -- this is the "El" case

end

partial def wellf (its eits : List InductiveType) (i : Nat := 0) (wits := []) : List InductiveType :=
if i >= its.length then wits else
let it  := its.get! i
let ctors := it.ctors.map fun ctor =>
  { name := ctor.name ++ wellfSuffix,
    type := wellfCtor its eits i ctor.name ctor.type : Constructor }
let wit := { name  := it.name ++ wellfSuffix,
             type  := wellfHeader its eits i,
             ctors := ctors : InductiveType }
wellf its eits (i + 1) (wits.append [wit])

end IIT
