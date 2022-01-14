/- Type Erasure for IITs -/

import Lean.Elab.Command
import Init.Data.Array.Basic

open Lean
open Elab
open Array
open Expr

namespace IIT
variable (its : List InductiveType)

def erasureSuffix : String := "E"

def eraseHeader : Expr → Expr := λ e => 
match e with
| forallE n f e x => eraseHeader e
| _ => e

def collectHeaderNames : Array Name :=
its.toArray.map InductiveType.name

def isHeaderApp (e : Expr) : Bool :=
match e with
| const n l d => contains (collectHeaderNames its) n
| app f e d   => isHeaderApp f
| _           => false

def addEIfHeader (n : Name) : Name :=
if contains (collectHeaderNames its) n then n ++ erasureSuffix
else n

def eraseCtor (e : Expr) : Expr :=
match e with
| forallE n t b d => mkForall n e.binderInfo (eraseCtor t) (eraseCtor b)
| lam n t b d     => mkLambda n e.binderInfo (eraseCtor t) (eraseCtor b)
| app f e d       => if isHeaderApp its f then eraseCtor f -- erase applications of sorts
                     else mkApp (eraseCtor f) (eraseCtor e)
| const n l d     => mkConst (addEIfHeader its n) l
| _               => e

def erase : List InductiveType :=
its.map fun it => { name := it.name ++ erasureSuffix, 
                    type := eraseHeader it.type,
                    ctors := it.ctors.map fun ctor => { name := ctor.name ++ erasureSuffix,
                                                        type := eraseCtor its ctor.type } }

end IIT
