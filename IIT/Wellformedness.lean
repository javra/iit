/- Wellformedness Predicate for IITs -/

import Lean.Elab
import Init.Data.Array.Basic

open Lean
open Elab
open Command
open Meta
open Expr
open Array

namespace IIT

def wellfSuffix : String := "w"

private def collectHeaderNames (its : List InductiveType) : Array Name :=
its.toArray.map InductiveType.name

private def headerAppIdx? (its : List InductiveType) (e : Expr) : Option Nat :=
match e with
| const n l d => getIdx? (collectHeaderNames its) n
| app f e d   => headerAppIdx? its f
| _           => none

instance : Inhabited InductiveType :=
⟨{ name := arbitrary, type := arbitrary, ctors := arbitrary }⟩ 

def wellfHeader (its eits : List InductiveType) (i : Nat) (e : Expr := (its.get! i).type) : Expr :=
match e with
| sort _ _        => mkForall "e" BinderInfo.default (eits.get! i).type (mkSort levelZero)
| forallE n t b d => 
  match headerAppIdx? its t with
  | some j => mkForall n e.binderInfo (eits.get! j).type (wellfHeader its eits i b)
  | none   => mkForall n e.binderInfo t (wellfHeader its eits i b)
| lam n t b d     => mkLambda n e.binderInfo (wellfHeader its eits i t) (wellfHeader its eits i b) --TODO not sure if unreachable
| app f e d       => mkApp (wellfHeader its eits i f) e
| _ => e

partial def wellf (its eits : List InductiveType) (i : Nat := 0) (wits := []) : List InductiveType :=
if i >= its.length then wits else
let it := its.get! i
let wit := { name := it.name ++ wellfSuffix,
             type := wellfHeader its eits i,
             ctors := [] : InductiveType }
wellf its eits (i + 1) (wits.append [wit])

end IIT
