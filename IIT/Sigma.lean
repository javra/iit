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

/-
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
-/
variables (its eits wits : List InductiveType)

def mkSigma (l : Level) (α β : Expr) : Expr :=
mkApp (mkApp (mkConst `Sigma [l, levelZero]) α) β

def sigmaHeader (i : Nat) (e : Expr) : Expr :=
match e with
| sort l d => mkSigma l (mkConst (eits.get! i).name) (mkConst (wits.get! i).name)
| _ => e

#check @Sigma

end IIT
