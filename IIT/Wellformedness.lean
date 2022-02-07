/- Wellformedness Predicate for IITs -/

import Lean.Elab
import Init.Data.Array.Basic
import IIT.InductiveUtils
import IIT.Erasure
import IIT.Util

open Lean
open Expr
open Elab
open Command
open Meta
open Array

namespace IIT

def wellfSuffix : String := "w"

section

variable (its eits : List InductiveType)

--TODO move the next three defs into some util file
def headerAppIdx? (e : Expr) : Option Nat :=
match e with
| const n l d => getIdx? (collectHeaderNames its) n
| app f e d   => headerAppIdx? f
| _           => none

partial def ctorAppIdx?Aux (n : Name) (i := 0) : Option (Nat × Nat) :=
if i >= its.length then none else
match getIdx? ((its.get! i).ctors.toArray.map Constructor.name) n with
| some j => some (i, j)
| none   => ctorAppIdx?Aux n (i + 1)

def ctorAppIdx? (e : Expr) : Option (Nat × Nat) :=
match e with
| const n l d => ctorAppIdx?Aux its n
| app f e d   => ctorAppIdx? f
| _           => none

def wellfHeader (i : Nat) (e : Expr := (its.get! i).type) : Expr :=
match e with
| sort _ _        => mkForall "e" BinderInfo.default 
                      (mkConst $ (its.get! i).name ++ erasureSuffix) (mkSort levelZero)
| forallE n t b d => 
  match headerAppIdx? its t with
  | some j => mkForall n e.binderInfo 
                (mkConst $ (its.get! j).name ++ erasureSuffix) (wellfHeader i b)
  | none   => mkForall n e.binderInfo t (wellfHeader i b)
| _ => e

def addWIfHeader (n : Name) (l : List Level) : Expr :=
if contains (collectHeaderNames its) n then mkConst (n ++ wellfSuffix) l
else mkConst n l

def addEIfCtor (n : Name) (l : List Level) : Expr :=
let ctorss := its.map (λ it => it.ctors)
if ctorss.any (λ ctors => (ctors.map Constructor.name).contains n) then mkConst (n ++ erasureSuffix) l
else mkConst n l

def wellfCtorTmP (e : Expr) : Expr :=
match e with
| const n l _ => addEIfCtor its n l
| app f e _   => mkApp (wellfCtorTmP f) (wellfCtorTmP e)
| _           => e

def wellfCtorTmS (e : Expr) : Expr :=
match e with
| app f e _   => mkApp (wellfCtorTmS f) (wellfCtorTmP its e)
| const n l _ => addWIfHeader its n l
| _           => e

partial def wellfCtor (e eref : Expr) : Expr :=
match e with
| forallE n t b d =>
  match headerAppIdx? its t with
  | some j => mkForall (n ++ "e") BinderInfo.default (mkConst $ (eits.get! j).name) $
              mkForall (n ++ "w") b.binderInfo 
               (mkApp (liftBVarsOne (wellfCtorTmS its t)) (mkBVar 0)) $
               wellfCtor (liftBVarsOne b) (mkApp (liftBVarsTwo eref) (mkBVar 1))
  | none   => mkForall n e.binderInfo t $ 
              wellfCtor b (mkApp (liftBVarsOne eref) (mkBVar 0))
| _ => mkApp (wellfCtorTmS its e) eref

end

partial def wellf (its eits : List InductiveType) (i : Nat := 0) (wits : List InductiveType := []) : List InductiveType :=
if i >= its.length then wits else
let it  := its.get! i
let ctors := it.ctors.map fun ctor =>
  { name := ctor.name ++ wellfSuffix,
    type := wellfCtor its eits ctor.type (mkConst (ctor.name ++ erasureSuffix)) : Constructor }
let wit := { name  := it.name ++ wellfSuffix,
             type  := wellfHeader its i,
             ctors := ctors : InductiveType }
wellf its eits (i + 1) (wits.append [wit])

end IIT
